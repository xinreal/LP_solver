import java.io.File
import java.util.Locale
import kotlin.math.abs

enum class Sense { LE, GE, EQ } // типы сравнения
enum class Status { OPTIMAL, UNBOUNDED, INFEASIBLE } // статус задачи

data class Constraint(val a: DoubleArray, val sense: Sense, val b: Double)
data class LP(
    val maximize: Boolean,          // max -> true, min -> false
    val c: DoubleArray,            // коэф-ты целевой функции
    val constraints: List<Constraint> // список ограничений
)

data class Solution(
    val status: Status,
    val objective: Double? = null, // значение Z
    val x: DoubleArray? = null // найденный вектор x
)

/** ===== Parser ===== */
fun parseLP(path: String): LP {
    val lines = File(path).readLines()
        .map { it.trim() }
        .filter { it.isNotEmpty() && !it.startsWith("#") }

    fun String.afterColon(): String = substringAfter(":").trim() //расширение для String: подстрока после двоеточия
    var i = 0 //указатель текущей строки

    fun readKey(expected: String): String {
        require(
            lines[i].lowercase(Locale.US).startsWith("$expected:")
        ) { "Ожидалось '$expected:' в строке: ${lines[i]}" }
        return lines[i++].afterColon()
    }

    val objective = readKey("objective").lowercase(Locale.US)
    val maximize = when (objective) {
        "max" -> true
        "min" -> false
        else -> error("objective должен быть max или min")
    }

    val n = readKey("n").toInt()
    val m = readKey("m").toInt()

    require(lines[i].lowercase(Locale.US).startsWith("c:")) { "Ожидалось 'c:'" }
    val c = lines[i++].afterColon().split(Regex("\\s+")).map { it.toDouble() }.toDoubleArray()
    require(c.size == n) { "Длина вектора c (${"%d".format(c.size)}) ≠ n ($n)" }

    require(lines[i].lowercase(Locale.US).startsWith("constraints:")) { "Ожидалось 'constraints:'" }
    i++

    val constraints = mutableListOf<Constraint>()
    repeat(m) {
        val parts = lines[i++].split(Regex("\\s+")).filter { it.isNotEmpty() }
        require(parts.size >= n + 2) { "Строка ограничения слишком короткая: ${parts.joinToString(" ")}" }
        val a = DoubleArray(n) { idx -> parts[idx].toDouble() }
        val senseStr = parts[n]
        val sense = when (senseStr) {
            "<=", "≤" -> Sense.LE
            ">=", "≥" -> Sense.GE
            "=" -> Sense.EQ
            else -> error("Некорректный sense: $senseStr")
        }
        val b = parts[n + 1].toDouble()
        constraints += Constraint(a, sense, b)
    }

    return LP(maximize, c, constraints)
}

/** ===== Двухфазный симплекс на таблицах (x >= 0) =====
 * Преобразования:
 * - Для >=: умножаем строку на -1 → получаем <=
 * - Для =: оставляем как есть
 * Далее все неравенства <= приводим к равенствам добавлением слэков.
 * Для = после выравнивания добавляем искусственные переменные (Фаза I).
 * Для тех, что были изначально =, искусственная нужна сразу.
 */
class TwoPhaseSimplex(private val lp: LP) {

    private lateinit var tableau: Array<DoubleArray>
    private var numRows: Int = 0
    private var numCols: Int = 0

    // карты индексов переменных в таблице
    private var xStart = 0            // столбцы исходных переменных
    private var sStart = 0            // добавочная переменная
    private var aStart = 0            // искусственные
    private var rhsCol = 0            // свободные члены (b)

    private var n = lp.c.size   // количество переменных
    private var m = lp.constraints.size //количество ограничений
    private val rowIsArtificial = mutableListOf<Boolean>() // добавлялась ли искусственная переменная?

    // базис: для каждой строки (кроме целевой) запоминаем, какой столбец в базе
    private val basis = mutableListOf<Int>()

    /** ===== Приведение ограничений к '<=' ===== */
    private fun buildStandardized(): List<Constraint> {
        val out = mutableListOf<Constraint>()
        for (c in lp.constraints) {
            when (c.sense) {
                Sense.LE -> out += c
                Sense.GE -> { // умножаем на -1 → <=
                    val a = DoubleArray(n) { j -> -c.a[j] }
                    out += Constraint(a, Sense.LE, -c.b)
                }

                Sense.EQ -> out += c // там, где '=', пока оставляем как есть
            }
        }
        return out
    }

    /** Разделяем ограничения на <= и = (для подсчета кол-ва искусственных переменных) */
    private data class Structured(val eqs: List<Constraint>, val leqs: List<Constraint>)

    private fun splitBySense(std: List<Constraint>): Structured {
        val eqs = std.filter { it.sense == Sense.EQ }
        val leqs = std.filter { it.sense == Sense.LE }
        return Structured(eqs, leqs)
    }

    /** Строим таблицу для Фазы I: минимизируем сумму искусственных (т.е. в таблице – max(−∑a)) */
    private fun buildPhaseITableau(): Int {
        val std = buildStandardized()
        val (eqs, leqs) = splitBySense(std)

        val numSlack = leqs.size
        val numArtificial = eqs.size

        xStart = 0
        sStart = xStart + n
        aStart = sStart + numSlack
        rhsCol = aStart + numArtificial
        numCols = rhsCol + 1 // включая свободный член

        // инициализируем таблицу нулями
        numRows = m + 1
        tableau = Array(numRows) { DoubleArray(numCols) { 0.0 } }
        rowIsArtificial.clear()
        basis.clear()

        // Заполняем <= добавочными переменными
        var row = 0
        var sIdx = 0 // счетчик доп переменных
        var aIdx = 0 //счетчик искусственных переменных

        // Сначала все <=
        for (con in std) {
            val r = tableau[row]
            for (j in 0 until n) r[xStart + j] = con.a[j]   //расставляем кэфы для х
            r[rhsCol] = con.b                                    // b
            when (con.sense) {
                Sense.LE -> {                                    // если ≤
                    r[sStart + sIdx] = 1.0
                    basis += (sStart + sIdx)  // доп переменная
                    rowIsArtificial += false
                    sIdx++
                }

                Sense.EQ -> {                                    // если =
                    // = без добавочной переменной → искусственная = 1
                    r[aStart + aIdx] = 1.0
                    basis += (aStart + aIdx)  // базисная – искусственная
                    rowIsArtificial += true
                    aIdx++
                }

                else -> {}
            }
            row++
        }

        // Фаза I. Цель: минимизировать сумму искусственных переменных (∑a_i).
        // Для каждой искусственной переменной ставим коэффициент -1 в целевой строке
        val obj = tableau[numRows - 1]
        for (j in 0 until numCols) obj[j] = 0.0
        for (ai in 0 until numArtificial) {
            obj[aStart + ai] = -1.0
        }

        // Приводим целевую строку Фазы I к каноническому виду:
        // для каждой строки, где в базисе стоит искусственная переменная,
        // прибавляем эту строку к строке цели, чтобы обнулить коэффициент под a_i.
        for (rIdx in 0 until m) {
            val basicCol = basis[rIdx]  // индекс столбца базисной переменной в строке
            if (basicCol in aStart until aStart + numArtificial) { // если эта переменная искусственная
                for (j in 0 until numCols) obj[j] += tableau[rIdx][j]   // складываем с целевой строкой
            }
        }
        return numArtificial
    }

    /** Выбор столбца для базиса следующего шага */
    private fun blandEntering(rowObj: DoubleArray, start: Int, endExclusive: Int): Int? {
        for (j in start until endExclusive) {
            if (rowObj[j] > 1e-12) return j //ищем первый слева положительный коэффициент в целевой строке
        }
        return null
    }

    /** Ищем, какая переменная покинет базис */
    private fun leavingRow(enterCol: Int): Int? {
        var bestRow = -1
        var bestRatio = Double.POSITIVE_INFINITY
        for (i in 0 until m) {                  //перебираем все строки симплекс метода
            val a = tableau[i][enterCol]             // в каждой строке берем коэф. в выбранном столбце
            if (a > 1e-12) {                           // a > 0
                /** смотрим насколько можно увеличить переменную в выбранном столбце
                 * пока какая-то другая не стала нулем */
                val ratio = tableau[i][rhsCol] / a
                if (ratio < bestRatio - 1e-12 || (abs(ratio - bestRatio) <= 1e-12 && i < bestRow)) {
                    bestRatio = ratio       // в итоге мы выбираем строку с наименьшим отношением (b_i / a_ij)
                    bestRow = i
                }
            }
        }
        return if (bestRow == -1) null else bestRow // если таких строк нет - функция бесконечно растет
    }

    private fun pivot(pRow: Int, pCol: Int) {
        val pivot = tableau[pRow][pCol] // выбираем элемент, по которому будем делить
        for (j in 0 until numCols) tableau[pRow][j] /= pivot
        // зануляем этот столбец в остальных строках
        for (i in 0 until numRows) if (i != pRow) {
            val factor = tableau[i][pCol]
            if (abs(factor) > 1e-12) {
                for (j in 0 until numCols) {
                    tableau[i][j] -= factor * tableau[pRow][j]
                }
            }
        }
        basis[pRow] = pCol // обновляем массив базисных переменных
    }

    /**
    Алгоритм симплекс-итерации:
    1. Берём строку целевой функции (последняя строка tableau).
    2. Выбираем входящий столбец (blandEntering) — переменная, улучшающая цель.
       - Если входящего нет -> решение OPTIMAL.
    3. Для выбранного столбца ищем выходящую строку (leavingRow) по правилу min(b[i]/a[i,j]) для a>0.
       - Если выхода нет -> задача UNBOUNDED.
    4. Выполняем деление и обнуление по выбранному элементу таблицы по (leave, enter): нормируем pivot-строку и зануляем столбец в остальных строках (pivot()).
    5. Обновляем базис и повторяем шаги 1–4 до получения OPTIMAL или UNBOUNDED.
    P.S.:
    - Используется эвристика Бланда для предотвращения циклов (tie-break по индексам).
    - Для численной устойчивости применён эпсилон (1e-12) при сравнениях с нулём.
    */
    private fun runSimplex(allowedCols: IntRange): Status {
        while (true) {
            val obj = tableau[numRows - 1]
            val enter = blandEntering(obj, allowedCols.first, allowedCols.last + 1) ?: return Status.OPTIMAL
            val leave = leavingRow(enter) ?: return Status.UNBOUNDED
            pivot(leave, enter)
        }
    }
/** эта функция просто возвращает текущее значение целевой функции из симплекс-таблицы:
 *  берет последнюю строку (строку с функцией цели) и возвращает значение в столбце правых частей (RHS).*/
    private fun currentObjective(): Double = tableau[numRows - 1][rhsCol]

/** Собирает вектор исходных переменных x из текущего базисного решения:
* для каждой базисной строки, если базисный столбец принадлежит диапазону исходных x,
* записываем RHS в соответствующую позицию, остальные остаются 0.*/
    private fun extractX(): DoubleArray {
        val x = DoubleArray(n) { 0.0 }
        for (i in 0 until m) {
            val col = basis[i]
            if (col in xStart until xStart + n) {
                x[col - xStart] = tableau[i][rhsCol]
            }
        }
        return x
    }

    fun solve(): Solution {
        // Если задача на min – умножаем c на -1 и интерпретируем как max, восстановим знак в конце
        val sign = if (lp.maximize) 1.0 else -1.0

        // === Фаза I ===
// Построили таблицу для Фазы I (в ней есть искусственные переменные).
        val numArtificial = buildPhaseITableau()

// Разрешаем входить в базис только настоящим x и доп-переменным.
// Искусственные переменные остаются в таблице, но их мы не позволяем выбирать
// в качестве "входящего" столбца на этом этапе.
        val phaseICols = xStart until (aStart) // диапазон столбцов: x + s

// Запускаем симплекс для Фазы I, где пытаемся убрать искусственные переменные.
        val st1 = runSimplex(phaseICols)
        if (st1 == Status.UNBOUNDED) {
            // Теоретически такое редко возможно в Фазе I. Но если случилось —
            // возвращаем, что система ограничений не выполняется (невыполнима).
            return Solution(Status.INFEASIBLE)
        }

// Проверяем результат Фазы I: значение целевой должно быть 0.
// В Фазе I мы минимизируем сумму искусственных переменных.
// Если минимум не равен 0 — значит нельзя убрать искусственные → задача невыполнима.
        val phaseIObj = currentObjective()
        if (phaseIObj < -1e-8 || phaseIObj > 1e-8) {
            return Solution(Status.INFEASIBLE)
        }

// Удаляем столбцы с искусственными переменными из таблицы,
// чтобы перейти ко второй фазе с исходной целью.
// Новое число столбцов = количество столбцов до aStart (x + s) + столбец RHS.
        val newNumCols = (aStart) + 1 // x+s + rhs
        val newTab = Array(numRows) { DoubleArray(newNumCols) { 0.0 } }
        for (i in 0 until numRows) {
            // Копируем все колонки до aStart (это x и s), затем копируем RHS (свободный член).
            var col = 0
            for (j in 0 until aStart) {
                newTab[i][col++] = tableau[i][j]
            }
            newTab[i][col] = tableau[i][rhsCol] // rhs
        }

// Подменяем старую таблицу на новую без искусственных столбцов.
        tableau = newTab
        numCols = newNumCols
        rhsCol = numCols - 1

// Обновляем позиции начала блоков переменных
        xStart = 0
        sStart = xStart + n
// aStart больше не нужен — искусственные удалены

// После удаления столбцов индексы в basis могли "слететь" (указывать на несуществующие столбцы).
// Обычно искусственные переменные уже не в базисе, но на всякий случай попробуем
// заменить любой некорректный базисный столбец на реальный единичный столбец в x/s,
// если такой есть в той же строке.
        for (i in 0 until m) {
            val col = basis[i]
            if (col >= sStart + (tableau[0].size - n - 1 /*примерный пересчет*/)) {
                // Ищем столбец, который в текущей строке выглядит как единичный (1 в этой строке, 0 в остальных).
                var found = -1
                for (j in 0 until (numCols - 1)) {
                    if (abs(tableau[i][j] - 1.0) <= 1e-12) {
                        var unit = true
                        for (r in 0 until m) if (r != i && abs(tableau[r][j]) > 1e-12) {
                            // если в другой строке этот столбец не ноль — это не единичный столбец
                            unit = false; break
                        }
                        if (unit) {
                            found = j; break
                        }
                    }
                }
                if (found != -1) basis[i] = found
            }
        }

// Теперь задаём целевую функцию для Фазы II — это исходная целевая.
// Сначала обнуляем всю целевую строку.
        for (j in 0 until numCols) tableau[numRows - 1][j] = 0.0
// Затем записываем коэффициенты целевой для исходных переменных x (с учётом знака).
        for (j in 0 until n) tableau[numRows - 1][xStart + j] = sign * lp.c[j]

// Приводим целевую строку к каноническому виду по текущему базису:
// если какая-то базисная переменная имеет коэффициент в целевой строке,
// вычитаем из целевой строки соответствующую строку ограничения,
// чтобы в столбцах базиса стояли нули (как в нормальной симплекс-таблице).
        for (i in 0 until m) {
            val bj = basis[i]
            val coeff = tableau[numRows - 1][bj]
            if (abs(coeff) > 1e-12) {
                for (j in 0 until numCols) tableau[numRows - 1][j] -= coeff * tableau[i][j]
            }
        }

        // === Фаза II ===
        val st2 = runSimplex(xStart until (numCols - 1)) // x и s могут входить
        return when (st2) {
            Status.UNBOUNDED -> Solution(Status.UNBOUNDED)
            Status.OPTIMAL -> {
                val x = extractX()
                // считаем Z по определению, чтобы избежать путаницы со знаком
                val zByX = DoubleArray(lp.c.size) { j -> lp.c[j] * x[j] }.sum()
                val trueZ = if (lp.maximize) zByX else -zByX
                Solution(Status.OPTIMAL, trueZ, x)
            }

            else -> Solution(Status.INFEASIBLE)
        }
    }
}

/** ===== CLI ===== */
fun main(args: Array<String>) {
    try {
        val path = if (args.isNotEmpty()) args[0] else {
            // пробуем достать из ресурсов
            val url = {}.javaClass.getResource("/input.txt")
                ?: error("Не найден input.txt ни по аргументу, ни в resources.")
            // скопируем во временный файл, чтобы переиспользовать parseLP(File)
            val tmp = kotlin.io.path.createTempFile("lp_", ".txt").toFile()
            tmp.writeText(url.readText())
            tmp.absolutePath
        }
        val lp = parseLP(path)
        val solver = TwoPhaseSimplex(lp)
        val sol = solver.solve()
        when (sol.status) {
            Status.INFEASIBLE -> println("РЕЗУЛЬТАТ: невыполнимо.")
            Status.UNBOUNDED -> println("РЕЗУЛЬТАТ: неограничено.")
            Status.OPTIMAL -> {
                println("РЕЗУЛЬТАТ: оптимум найден.")
                println("Z* = ${"%.6f".format(sol.objective)}")
                sol.x!!.forEachIndexed { i, v -> println("x${i + 1} = ${"%.6f".format(v)}") }
            }
        }
    } catch (e: Exception) {
        System.err.println("Ошибка: ${e.message}")
    }
}
