package ru.itmo.mit.supercompiler

import org.testng.Assert.*
import org.testng.annotations.*
import ru.itmo.mit.supercompiler.Constructor.Companion.num
import ru.itmo.mit.supercompiler.Constructor.Companion.succ
import ru.itmo.mit.supercompiler.Constructor.Companion.zero

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
}