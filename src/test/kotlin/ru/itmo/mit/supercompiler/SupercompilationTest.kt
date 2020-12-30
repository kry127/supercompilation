package ru.itmo.mit.supercompiler

import org.testng.Assert.*
import org.testng.annotations.*
import ru.itmo.mit.supercompiler.Constructor.Companion.cons
import ru.itmo.mit.supercompiler.Constructor.Companion.fls
import ru.itmo.mit.supercompiler.Constructor.Companion.nil
import ru.itmo.mit.supercompiler.Constructor.Companion.num
import ru.itmo.mit.supercompiler.Constructor.Companion.succ
import ru.itmo.mit.supercompiler.Constructor.Companion.tru
import ru.itmo.mit.supercompiler.Constructor.Companion.zero
import ru.itmo.mit.supercompiler.SupercompilationTest.KnuthMorrisPrattABCD.letters
import java.lang.Integer.max
import java.lang.Integer.min
import java.lang.StringBuilder
import kotlin.random.Random
import kotlin.system.measureNanoTime

class SupercompilationTest {

    /// dataset definitions
    @DataProvider(name = "tenNaturals")
    fun getTenNaturals(@TestInstance `object`: Any): Array<Array<Any>> {
        val data = (1..10).map { arrayOf(it as Any) }.toTypedArray()
        return data
    }

    @DataProvider(name = "naturalPairs")
    fun getNaturalPairs(@TestInstance `object`: Any): Array<Array<Any>> {
        val data = (1..10).flatMap { n1 -> (1..10).map { n2 -> arrayOf((n1 to n2) as Any)} }.toTypedArray()
        return data
    }


    @DataProvider(name = "someStrings")
    fun getSomeStrings(@TestInstance `object`: Any): Array<Array<Any>> {

        val data = (1..10).flatMap {
            val pattern = (1..Random.nextInt(1, 5)).fold("") {s, c -> s + letters.random()}

            val data = (1..50).map {
                (1..Random.nextInt(1, 25)).fold("") {s, c -> s + letters.random()}
            }.map {
                // try do distribute examples evenly
                if (Random.nextFloat() < 0.5) {
                    it.replace(pattern, "")
                } else {
                    StringBuilder(it).insert(Random.nextInt(it.length), pattern).toString()
                }
            }
                .map { arrayOf(pattern as Any, it as Any) }
            data
        }
        return data.toTypedArray()
    }

    fun getFixedSizedStrings(patternSize : Int, stringSize : Int, datasetSize : Int) : Pair<String, List<String>> {
        val pattern = (1..patternSize).fold("") {s, c -> s + letters.random()}

        val data = (1..datasetSize).map {
            (1..stringSize).fold("") {s, c -> s + letters.random()}
        }.map {
            // try do distribute examples evenly
            if (Random.nextFloat() < 0.5) {
                it.replace(pattern, "")
            } else {
                val beginPos = Random.nextInt(max(it.length - pattern.length, 1))
                StringBuilder(it)
                    .replace(beginPos, beginPos + pattern.length, pattern)
                    .toString()
            }
        }
        return pattern to data
    }

    /// Tests
    @Test
    fun youBetterWork_debugOutput() {
        val prog = CommonExpressions.sumSquaresN(Var("n"))
        val newprog = supercompile(prog, debug = true)
        print(newprog)
    }


    @Test(dataProvider = "tenNaturals")
    fun testProgramsExtentionality(N : Int) {
        val nname = "n"
        // supercompile our sumSqareN
        val regular_lam = CommonExpressions.sumSquaresN(Var(nname))
        val supercompiled_lam = supercompileProgram(regular_lam)
        // abstract both by variable n
        val regular = regular_lam.fmap { this abs  "n" }
        val supercompiled = supercompiled_lam.fmap { this abs  "n" }

        // then check outputs are the same -- apply values and normalize
        val regularResult = regular.fmap {this app num(N)} .hnf()
        val supercompiledResult = supercompiled.fmap {this app num(N)} .hnf()
        assertTrue(regularResult.expression isomorphic supercompiledResult.expression)

    }

    // https://github.com/sergei-romanenko/spsc-idris/blob/master/tasks/mult_a_b.task
    object MultiplicationProgram {
        val targetexpr = Function("mult") app (Var ("a")) app (Var ("b"))
        val add = listOf("x", "y") arrow makeCase(Var("x"),
            makePattern("Z") to Var("y"),
            makePattern("S", "x")  to (Function("add") app Var("x") app Var("y")).succ()
        )
        val mult = listOf("x", "y") arrow makeCase(Var("x"),
            makePattern("Z") to zero,
            makePattern("S", "x") to (Function("add") app
                    (Function("mult") app Var("x") app Var("y")) app (Var("y")))
        )
        val program = Let("add", add, Let("mult", mult, targetexpr))
    }

    @Test
    fun multiplication() {
        val prog = MultiplicationProgram.program.toProgram()
        print(prog)
        val newprog = supercompile(prog, debug = true)
        print(newprog)
    }

    @Test(dataProvider = "naturalPairs")
    fun multiplication_testProgramsExtentionality(pair: Any) {
        val (m, n) = pair as Pair<Int, Int>

        val prog = MultiplicationProgram.program
        val supercompiled_prog = supercompile(prog.toProgram())

        val regular = prog abs "a" abs "b"
        val supercompiled = supercompiled_prog  abs  "a" abs "b"

        val regularResult = (regular app num(m) app num(n)).toProgram().hnf()
        val supercompiledResult = (supercompiled app num(m) app num(n)).toProgram().hnf()
        assertTrue(regularResult.expression isomorphic supercompiledResult.expression)

    }

    object KnuthMorrisPrattABCD {
        // https://github.com/sergei-romanenko/spsc-idris/blob/master/tasks/kmp_A.task

        val letters = "ABCD"

        fun buildKmpString(s : String) : Constructor {
            return s.foldRight(nil) {ch, acc -> Constructor(ch.toString()) cons acc}
        }

        val pA = makePattern("A")
        val pB = makePattern("B")
        val pC = makePattern("C")
        val pD = makePattern("D")

        val ite = listOf("c", "x", "y") arrow (makeCase(Var("c"),
            Pattern.patTrue to Var("x"),
            Pattern.patFalse to Var("y")
        ))
        val eqA = listOf("x") arrow (makeCase(Var("x"),
            pA to tru,
            pB to fls,
            pC to fls,
            pD to fls,
        ))
        val eqB = listOf("x") arrow (makeCase(Var("x"),
            pA to fls,
            pB to tru,
            pC to fls,
            pD to fls,
        ))
        val eqC = listOf("x") arrow (makeCase(Var("x"),
            pA to fls,
            pB to fls,
            pC to tru,
            pD to fls,
        ))
        val eqD = listOf("x") arrow (makeCase(Var("x"),
            pA to fls,
            pB to fls,
            pC to fls,
            pD to tru,
        ))
        val eqSymb = listOf("x", "y") arrow (makeCase(Var("x"),
            pA to (Function("eqA") app Var("y")),
            pB to (Function("eqB") app Var("y")),
            pC to (Function("eqC") app Var("y")),
            pD to (Function("eqD") app Var("y")),
        ))

        val match = listOf("p", "s") arrow (Function("m") app listOf("p", "s", "p", "s").map { Var(it) })
        // check pattern (pp). If exhausted, return true (we matched it!)
        // otherwise decompose pattern p : pp, and try to match string "ss"
        // parameters op and os tracks current position
        val m = listOf("pp", "ss", "op", "os") arrow (makeCase(Var("pp"),
            Pattern.patNil to tru,
            Pattern.patCons("p", "pp") to (Function("mx") app listOf("ss", "p", "pp", "op", "os").map {Var(it)})
        ))

        val mx = listOf("ss", "p", "pp", "op", "os") arrow (makeCase(Var("ss"),
            Pattern.patNil to fls,
            Pattern.patCons("s", "ss") to (Function("ite")
                    app (Function("eqSymb") app listOf("p", "s").map{Var(it)})
                    app (Function("m") app listOf("pp", "ss", "op", "os").map { Var(it) }) // if success advance string
                    app (Function("mn") app listOf("os", "op").map { Var(it) }) // otherwise reset to current position 'op, os'
                    )
        ))

        val mn = listOf("os", "op") arrow (makeCase(Var("os"),
            Pattern.patNil to fls,
            Pattern.patCons("s", "ss") to (Function("m") app listOf("op", "ss", "op", "ss").map {Var(it)})
        ))

        // define context for target expression
        val context : Where = mapOf(
            "eqA" to eqA, "eqB" to eqB, "eqC" to eqC, "eqD" to eqD, "eqSymb" to eqSymb, "ite" to ite,
            "match" to match, "m" to m, "mx" to mx, "mn" to mn
        )

        fun buildProgram(pattern : String) : Program {
            return (Function("match") app buildKmpString(pattern) app (Var ("str"))).toProgram(context)
        }

    }


    @Test
    fun kmpTest_ApearanceAndAbsence() {
        val kmpFinder = KnuthMorrisPrattABCD.buildProgram("A")

        fun testInstance(string : String, contains : Boolean) {
            val stringAsTerm = KnuthMorrisPrattABCD.buildKmpString(string)
            val reducible = kmpFinder.fmap { (this abs "str") app stringAsTerm }
            if (contains) {
                assertTrue(reducible.hnf().expression isomorphic tru)
            } else {
                assertTrue(reducible.hnf().expression isomorphic fls)
            }
        }

        testInstance("ABAB", true)
        testInstance("BCBC", false)
    }

    @Test
    fun kmpTest_ABAC() {
        val kmpFinder = KnuthMorrisPrattABCD.buildProgram("ABAC")

        fun testInstance(string : String, contains : Boolean) {
            val stringAsTerm = KnuthMorrisPrattABCD.buildKmpString(string)
            val reducible = kmpFinder.fmap { (this abs "str") app stringAsTerm }
            if (contains) {
                assertTrue(reducible.hnf().expression isomorphic tru)
            } else {
                assertTrue(reducible.hnf().expression isomorphic fls)
            }
        }

        testInstance("ABABABABA", false)
        testInstance("ABAC", true)
        testInstance("ABA", false)
        testInstance("BAC", false)
        testInstance("ABBAC", false)
        testInstance("ABDACADABDA", false)
        testInstance("DCDBDABACAD", true)
    }


    @Test
    fun kmpSupercompilation() {
        val kmpFinder = KnuthMorrisPrattABCD.buildProgram("ABAC")
        print(kmpFinder)
        val newprog = supercompile(kmpFinder, debug = true)
        print(newprog)
    }


    @Test(dataProvider = "someStrings")
    fun kmpExtensionalityTest(pattern : String, input : String) {
        val kmpFinder = KnuthMorrisPrattABCD.buildProgram(pattern)
        val supercompiledFinder = supercompile(kmpFinder, debug = false)

        val stringAsTerm = KnuthMorrisPrattABCD.buildKmpString(input)
        val regularResult = kmpFinder.fmap { (this abs "str") app stringAsTerm }
        val superResult = (supercompiledFinder abs "str" app stringAsTerm).toProgram()
        assertTrue(regularResult.hnf().expression isomorphic superResult.hnf().expression)
    }



    @Test
    fun kmpPerformanceTest() {
        // testing grid
        val patternSize = listOf(1, 2, 3, 4, 5) // columns
        val inputSize = listOf(5, 10, 15, 20, 25) // rows
        val groupDatasetSize = 50

        // results stored here
        val originalProgramResult = mutableMapOf<Pair<Int, Int>, Double>()
        val supercompiledProgramResults = mutableMapOf<Pair<Int, Int>, Double>()


        fun calculate(patternSize: Int, inputSize: Int, datasetSize: Int) {
            // extract data
            val dataset = getFixedSizedStrings(patternSize, inputSize, datasetSize)
            val (pattern, strings) = dataset

            // prepare programs for pattern
            val kmpFinder = KnuthMorrisPrattABCD.buildProgram(pattern)
            val supercompiledFinder = supercompile(kmpFinder, debug = false)

            var sumOriginalPerformance = .0
            var sumSuperdompiledPerformance = .0
            for (input in strings) {
                // preparing subprograms
                val stringAsTerm = KnuthMorrisPrattABCD.buildKmpString(input)
                val regularTerm = kmpFinder.fmap { (this abs "str") app stringAsTerm }
                val superTerm = (supercompiledFinder abs "str" app stringAsTerm).toProgram()

                // launch execution of original version of the program
                val time1 = measureNanoTime {
                    // just normalize, no need to check result in performance test
                    regularTerm.hnf()
                }
                // and then measure supercompiled version
                val time2 = measureNanoTime {
                    superTerm.hnf()
                }

                sumOriginalPerformance += time1 / 1000000000.0
                sumSuperdompiledPerformance += time2 / 1000000000.0
            }

            // when cycle is over, add info to the final result
            originalProgramResult[patternSize to inputSize] = sumOriginalPerformance / datasetSize
            supercompiledProgramResults[patternSize to inputSize] = sumSuperdompiledPerformance / datasetSize
        }

        // perform computations
        for (patSz in patternSize) {
            for (inpSz in inputSize) {
                println("Computing with parameters patternSize=$patSz, inputSize=$inpSz, datasetSize=$groupDatasetSize")
                calculate(patSz, inpSz, groupDatasetSize)
            }
        }

        // output table

        println()
        println(" === ")
        println()
        println("Task has been done!")
        println("Performance table:")

        val columnWidth = 15
        val columnCount = patternSize.size + 1
        val widthLimit = columnCount * (columnWidth + 1) - 1
        val globalDelimiter = "+" + "-".repeat(widthLimit) + "+"
        fun globalFormatter(arg : Any?) : String {
            val prepared =  "+" + " ".repeat(widthLimit) + "+"
            val content = arg.toString()
            val start = max((widthLimit - content.length) / 2, 1)
            val end = min(start + content.length, prepared.length - 1)
            return prepared.replaceRange(start, end, content)
        }

        val delimiter = "+" + ("-".repeat(columnWidth) + "+").repeat(columnCount)
        fun formatter(args : List<Any?>) = args.fold("|") { str, smth -> str + " %${columnWidth - 2}s |".format(smth) }
        fun printTableForResult(result : Map<Pair<Int, Int>, Double>) {
            println(delimiter)
            println(formatter(listOf("") + patternSize))
            println(delimiter)
            for (inpSz in inputSize) {
                println(formatter(listOf(inpSz) + patternSize.map { "%.2f".format(result[it to inpSz])}))
                println(delimiter)
            }
        }

        val superheader = " pattern size |                                  input size                               "
        println(globalDelimiter)
        println(globalFormatter("Results of original program"))
        println(globalDelimiter)
        println(globalFormatter(superheader))
        printTableForResult(originalProgramResult)

        println()

        println(globalDelimiter)
        println(globalFormatter("Results of supercompiled program"))
        println(globalDelimiter)
        println(globalFormatter(superheader))
        printTableForResult(supercompiledProgramResults)

        println()
        println("The time measures in seconds.")
        println("There is average of $groupDatasetSize measures in one cell of the table!")
        println()
    }
}