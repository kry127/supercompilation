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
import kotlin.random.Random

class SupercompilationTest {

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
        val letters = "ABCD"

        val data = (1..50).map {
            (1..Random.nextInt(1, 10)).fold("") {s, c -> s + letters.random()}
        }.map { arrayOf(it as Any) }.toTypedArray()
        return data
    }

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
    fun kmpExtensionalityTest(input : String) {
        val kmpFinder = KnuthMorrisPrattABCD.buildProgram("ABAC")
        val supercompiledFinder = supercompile(kmpFinder, debug = false)

        val stringAsTerm = KnuthMorrisPrattABCD.buildKmpString(input)
        val regularResult = kmpFinder.fmap { (this abs "str") app stringAsTerm }
        val superResult = (supercompiledFinder abs "str" app stringAsTerm).toProgram()
        assertTrue(regularResult.hnf().expression isomorphic superResult.hnf().expression)
    }
}