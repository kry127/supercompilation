package ru.itmo.mit.supercompiler.ast

import org.testng.Assert.*
import org.testng.annotations.Test
import ru.itmo.mit.supercompiler.ast.CommonExpressions.K
import ru.itmo.mit.supercompiler.ast.CommonExpressions.K2
import ru.itmo.mit.supercompiler.ast.CommonExpressions.lamChurch
import ru.itmo.mit.supercompiler.ast.CommonExpressions.lamChurchSuc
import ru.itmo.mit.supercompiler.ast.CommonExpressions.lamChurchZ
import ru.itmo.mit.supercompiler.ast.CommonExpressions.id
import ru.itmo.mit.supercompiler.ast.CommonExpressions.list_empty
import ru.itmo.mit.supercompiler.ast.CommonExpressions.list_size
import ru.itmo.mit.supercompiler.ast.CommonExpressions.list_size_lambdaChurch
import ru.itmo.mit.supercompiler.ast.CommonExpressions.list_xyz
import ru.itmo.mit.supercompiler.ast.CommonExpressions.omega
import ru.itmo.mit.supercompiler.ast.CommonExpressions.omegaBig
import ru.itmo.mit.supercompiler.ast.Constructor.Companion.cons
import ru.itmo.mit.supercompiler.ast.Constructor.Companion.nil
import ru.itmo.mit.supercompiler.ast.Constructor.Companion.num

fun printTerm(term : String) {
    if (term.contains('\n')) {
        println("==============")
        println(term)
        println()
    } else {
        println("    $term")
    }
}

fun stepByStepPrinter(expr : Expr) {
    println("Step by step reduction of $expr")
    for (term in whnfSeq0(expr.renamedBoundVariables())) {
        printTerm("$term")
    }
}

fun stepByStepPrinter(expr : Program) {
    println("Step by step reduction of $expr")
    for (term in expr.hnfSeq()) {
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
        assertNull(whnfBetaReduction0(id))
    }
    @Test
    fun reductionTest_null2() {
        assertNull(whnfBetaReduction0(K))
    }
    @Test
    fun reductionTest_null3() {
        assertNull(whnfBetaReduction0(lamChurch(7)))
    }
    @Test
    fun reductionTest_suc2_is_WHNF() {
        assertNull(whnfBetaReduction0(lamChurchSuc(lamChurch(2))))
    }

    @Test
    fun reductionTest_omegaToOmega() {
        assertTrue(whnfBetaReduction0(omegaBig)!!.isomorphic(omegaBig))
    }
    @Test
    fun whnfTest_suc2xy_is_3xy() {
        val x = Var("p")
        val y = Var("q")

        val suc2xy = lamChurchSuc(lamChurch(2)).app(x).app(y).renamedBoundVariables()
        val suc2xy_nf = whnf0(suc2xy)
        stepByStepPrinter(suc2xy)
        println("$suc2xy ->* $suc2xy_nf")

        val c3xy = lamChurch(3).app(x).app(y).renamedBoundVariables()
        val c3xy_nf = whnf0(c3xy)
        stepByStepPrinter(c3xy)
        println("$c3xy ->* $c3xy_nf")

        // equals because they have the same variables
        assertTrue(suc2xy_nf.equals(c3xy_nf))
    }

    @Test
    fun patternMatching_list_xyz_empty() {
        stepByStepPrinter(list_empty.app(list_xyz))
        val res = whnf0(list_empty.app(list_xyz).renamedBoundVariables())
        assertTrue(res.isomorphic(lamChurchZ))
    }

    @Test
    fun patternMatching_list_xyz_length_church_numerals() {
        // to break WHNF add some globals
        val u = Var("u")
        val v = Var("v")
        val term = list_size_lambdaChurch.fmap { app(list_xyz).app(u).app(v) }
        stepByStepPrinter(term)
        val res = term.whnf().expression
        val cmpWith = whnf0(lamChurch(3).app(u).app(v))
        assertTrue(res.isomorphic(cmpWith))
    }

    @Test
    fun patternMatching_list_xyz_length() {
        val term = list_size.fmap { app(list_xyz) }
        stepByStepPrinter(term)
        // to break WHNF add some globals
        val res = term.hnf().expression
        val cmpWith = whnf0(num(3))
        assertTrue(res.isomorphic(cmpWith))
    }
}