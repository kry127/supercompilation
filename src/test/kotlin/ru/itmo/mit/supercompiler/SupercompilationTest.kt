package ru.itmo.mit.supercompiler

import org.testng.Assert.*
import org.testng.annotations.Test
import ru.itmo.mit.supercompiler.Constructor.Companion.num

class SupercompilationTest {
    @Test
    fun youBetterWork_debugOutput() {
        val prog = CommonExpressions.sumSquaresN(Var("n"))
        val newprog = supercompile(prog, debug = true)
        print(newprog)
    }
}