package ru.itmo.mit.supercompiler

import org.testng.Assert.*
import org.testng.annotations.Test
import ru.itmo.mit.supercompiler.CommonExpressions.K
import ru.itmo.mit.supercompiler.CommonExpressions.K2
import ru.itmo.mit.supercompiler.CommonExpressions.Num.letMul
import ru.itmo.mit.supercompiler.CommonExpressions.Num.letSum
import ru.itmo.mit.supercompiler.CommonExpressions.lamChurch
import ru.itmo.mit.supercompiler.CommonExpressions.lamChurchSuc
import ru.itmo.mit.supercompiler.CommonExpressions.lamChurchZ
import ru.itmo.mit.supercompiler.CommonExpressions.id
import ru.itmo.mit.supercompiler.CommonExpressions.list_empty
import ru.itmo.mit.supercompiler.CommonExpressions.list_size
import ru.itmo.mit.supercompiler.CommonExpressions.list_size_lambdaChurch
import ru.itmo.mit.supercompiler.CommonExpressions.list_xyz
import ru.itmo.mit.supercompiler.CommonExpressions.omega
import ru.itmo.mit.supercompiler.CommonExpressions.omegaBig
import ru.itmo.mit.supercompiler.CommonExpressions.sumSquaresN
import ru.itmo.mit.supercompiler.Constructor.Companion.cons
import ru.itmo.mit.supercompiler.Constructor.Companion.fls
import ru.itmo.mit.supercompiler.Constructor.Companion.nil
import ru.itmo.mit.supercompiler.Constructor.Companion.num
import ru.itmo.mit.supercompiler.Constructor.Companion.tru
import ru.itmo.mit.supercompiler.Function.Companion.leq
import ru.itmo.mit.supercompiler.Function.Companion.mult
import ru.itmo.mit.supercompiler.Function.Companion.plus
import org.testng.annotations.TestInstance

import org.testng.annotations.DataProvider




fun printTerm(term : String) {
    if (term.contains('\n')) {
        println("==============")
        println(term)
        println()
    } else {
        println("    $term")
    }
}

fun stepByStepPrinter(expr : Program, maxReductions : Int = 200) {
    println("Step by step reduction of $expr")
    var reductionsLeft = maxReductions
    for (term in expr.hnfSeq()) {
        if (reductionsLeft <= 0) error("Reduction limit exceeded")
        reductionsLeft -= 1
        val toPrint = "$term"
        printTerm("$term")
    }
}

class ExprTest {

    @Test
    fun monitorPrettyPrinting() {
        println("id = $id")
        println("K = $K")
        println("K2 = $K2")
        println("omega = $omega")
        println("omegaBig = $omegaBig")
        println("churchZ = $lamChurchZ")
        println("5 = ${lamChurch(5)}")
        println("suc (2)  =  ${lamChurchSuc(lamChurch(2))}")
        println("[] = $nil")
        println("list_xyz = $list_xyz")
        println(omega.cons(id).cons(Var("haha")).cons(Var("x").app(Var("y"))).cons(omegaBig))
        println("list_empty = $list_empty")
        println("list_size = $list_size_lambdaChurch")
        println("3+1=${letSum(num(3) plus num(1))}")

    }

    // isomorphic testing
    @Test
    fun isomorphicTest_K_is_not_churchZ() {
        assertFalse(K.isomorphic(lamChurchZ))
    }
    @Test
    fun isomorphicTest_K2_is_churchZ() {
        assertTrue(K2.isomorphic(lamChurchZ))
    }
    @Test
    fun isomorphicTest_K2repeatedArg_is_K2() {
        assertTrue(Lambda("t", Lambda("t", Var("t"))).isomorphic(K2))
    }

    @Test
    fun reductionTest_null1() {
        assertNull(id.toProgram().hnfBetaReduction())
    }
    @Test
    fun reductionTest_null2() {
        assertNull(K.toProgram().hnfBetaReduction())
    }
    @Test
    fun reductionTest_null3() {
        assertNull(lamChurch(7).toProgram().hnfBetaReduction())
    }
    @Test
    fun reductionTest_suc2_is_not_HNF() {
        assertNotNull(lamChurchSuc(lamChurch(2)).toProgram().hnfBetaReduction())
    }
    @Test
    fun reductionTest_suc2_is_WHNF() {
        assertNull(lamChurchSuc(lamChurch(2)).toProgram().whnfBetaReduction())
    }

    @Test
    fun reductionTest_omegaToOmega() {
        assertTrue(omegaBig.toProgram().hnfBetaReduction()?.expression?.isomorphic(omegaBig) ?: false)
    }
    @Test
    fun whnfTest_suc2xy_is_3xy() {
        val x = Var("p")
        val y = Var("q")

        val suc2xy = lamChurchSuc(lamChurch(2)).app(x).app(y).toProgram()
        val suc2xy_nf = suc2xy.whnf().expression
        stepByStepPrinter(suc2xy)
        println("$suc2xy ->* $suc2xy_nf")

        val c3xy = lamChurch(3).app(x).app(y).toProgram()
        val c3xy_nf = c3xy.whnf().expression
        stepByStepPrinter(c3xy)
        println("$c3xy ->* $c3xy_nf")

        // equals because they have the same variables
        assertTrue(suc2xy_nf.equals(c3xy_nf))
    }

    @Test
    fun patternMatching_list_xyz_empty() {
        val prog = list_empty.fmap{app(list_xyz)}
        stepByStepPrinter(prog)
        assertTrue(prog.whnf().expression.isomorphic(lamChurchZ))
    }

    @Test
    fun patternMatching_list_xyz_length_church_numerals() {
        // to break WHNF add some globals
        val u = Var("u")
        val v = Var("v")
        val term = list_size_lambdaChurch.fmap { app(list_xyz).app(u).app(v) }
        stepByStepPrinter(term)
        val res = term.whnf().expression
        val cmpWith = lamChurch(3).app(u).app(v).toProgram().whnf().expression
        assertTrue(res.isomorphic(cmpWith))
    }

    @Test
    fun patternMatching_list_xyz_length() {
        val term = list_size.fmap { app(list_xyz) }
        stepByStepPrinter(term)
        // to break WHNF add some globals
        val res = term.hnf().expression
        val cmpWith = num(3)
        assertTrue(res.isomorphic(cmpWith))
    }


    // church numerals tests
    @Test
    fun churchNumerals_addOneLeft() {
        val term = num(3) plus num(1)
        val prog = Program.convertToProgram(letSum(term))
        stepByStepPrinter(prog)
        // assert equals
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(num(4)))
    }

    @Test
    fun churchNumerals_addOneRight() {
        val term = num(1) plus num(3)
        val prog = Program.convertToProgram(letSum(term))
        stepByStepPrinter(prog)
        // assert equals
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(num(4)))
    }


    @Test
    fun churchNumerals_addSomeNaturals() {
        fun testWith(i : Int, j : Int) {
            val term = num(i) plus num(j)
            val prog = Program.convertToProgram(letSum(term))
            // assert equals
            val res = prog.hnf().expression
            assertTrue(res.isomorphic(num(i + j)))
        }
        for (i in 0..10) {
            for (j in 0..10) {
                testWith(i, j)
            }
        }
    }

    @Test
    fun churchNumerals_multiplyByOneLeft() {
        val term = num(1) mult num(3)
        val prog = Program.convertToProgram(letMul(letSum(term)))
        stepByStepPrinter(prog)
        // assert equals
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(num(3)))
    }


    @Test
    fun churchNumerals_multiplyByOneRight() {
        val term = num(3) mult num(1)
        val prog = Program.convertToProgram(letMul(letSum(term)))
        stepByStepPrinter(prog)
        // assert equals
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(num(3)))
    }


    @Test
    fun churchNumerals_multiplySomeNaturals() {
        fun testWith(i : Int, j : Int) {
            val term = num(i) mult num(j)
            val prog = Program.convertToProgram(letMul(letSum(term)))
            // assert equals
            val res = prog.hnf().expression
            assertTrue(res.isomorphic(num(i * j)))
        }
        for (i in 0..10) {
            for (j in 0..10) {
                testWith(i, j)
            }
        }
    }

    @Test
    fun churchNumerals_multiplyLargeNumbers_builtins() {
        val term = num(50) mult num(12)
        val prog = Program.convertToProgram(term)
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(num(50 * 12)))
    }

    @Test
    fun churchNumerals_multiplyLargeNumbersInv_builtins() {
        val term = num(12) mult num(50)
        val prog = Program.convertToProgram(term)
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(num(50 * 12)))
    }

    @Test
    fun churchNumerals_multiplyLargeNumbers_noBuiltins() {
        val term = num(50) mult num(12)
        val prog = Program.convertToProgram(letMul(letSum(term)))
        val res = prog.hnf_noBuiltins().expression
        assertTrue(res.isomorphic(num(50 * 12)))
    }

    @Test
    fun churchNumerals_multiplyLargeNumbersInv_noBuiltins() {
        val term = num(12) mult num(50)
        val prog = Program.convertToProgram(letMul(letSum(term)))
        val res = prog.hnf_noBuiltins().expression
        assertTrue(res.isomorphic(num(50 * 12)))
    }


    // Test inequalities
    @Test
    fun churchNumerals_3_leq_1() {
        val term = num(3) leq num(1)
        val prog = Program.convertToProgram(term)
        stepByStepPrinter(prog)
        // assert equals
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(fls))
    }

    @Test
    fun churchNumerals_1_leq_3() {
        val term = num(1) leq num(3)
        val prog = Program.convertToProgram(term)
        stepByStepPrinter(prog)
        // assert equals
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(tru))
    }

    @Test
    fun churchNumerals_2_leq_2() {
        val term = num(2) leq num(2)
        val prog = Program.convertToProgram(term)
        stepByStepPrinter(prog)
        // assert equals
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(fls))
    }

    // sample program -- sumSquares test
    @Test
    fun sampleProgram_output() {
        val N = 1
        val prog = sumSquaresN(num(N))
        stepByStepPrinter(prog)
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(num(1)))
    }

    // sample program -- sumSquares test
    @Test(dataProvider = "tenNaturals")
    fun sampleProgram_testSumSquares(N : Int) {
        val prog = sumSquaresN(num(N))
        val res = prog.hnf().expression
        assertTrue(res.isomorphic(num((1..N).map { it*it }.sum())))
    }

    @DataProvider(name = "tenNaturals")
    fun getData(@TestInstance `object`: Any): Array<Array<Any>> {
        val data = (1..20).map { arrayOf(it as Any) }.toTypedArray()
        return data
    }

}