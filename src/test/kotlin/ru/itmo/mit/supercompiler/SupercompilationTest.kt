package ru.itmo.mit.supercompiler

import org.testng.Assert.*
import org.testng.annotations.*
import ru.itmo.mit.supercompiler.Constructor.Companion.num

class SupercompilationTest {
    @Test
    fun youBetterWork_debugOutput() {
        val prog = CommonExpressions.sumSquaresN(Var("n"))
        val newprog = supercompile(prog, debug = true)
        print(newprog)
    }


    @Test(dataProvider = "tenNaturals")
    fun testProgramsExtentionally(N : Int) {
        val nname = "n"
        // supercompile our sumSqareN
        val regular_lam = CommonExpressions.sumSquaresN(Var(nname))
        val supercompiled_lam = supercompile(regular_lam)
        // abstract both by variable n
        val regular = regular_lam.fmap { this abs  "n" }
        val supercompiled = regular_lam.fmap { this abs  "n" }

        // then check outputs are the same -- apply values and normalize
        val regularResult = regular.fmap {this app num(N)} .hnf()
        val supercompiledResult = supercompiled.fmap {this app num(N)} .hnf()
        assertTrue(regularResult.expression isomorphic supercompiledResult.expression)

    }

    @DataProvider(name = "tenNaturals")
    fun getData(@TestInstance `object`: Any): Array<Array<Any>> {
        val data = (1..10).map { arrayOf(it as Any) }.toTypedArray()
        return data
    }
}