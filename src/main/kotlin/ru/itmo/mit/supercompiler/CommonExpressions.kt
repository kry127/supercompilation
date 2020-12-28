package ru.itmo.mit.supercompiler

import ru.itmo.mit.supercompiler.CommonExpressions.Num.mult
import ru.itmo.mit.supercompiler.CommonExpressions.Num.plus
import ru.itmo.mit.supercompiler.Constructor.Companion.cons
import ru.itmo.mit.supercompiler.Constructor.Companion.nil
import ru.itmo.mit.supercompiler.Constructor.Companion.succ
import ru.itmo.mit.supercompiler.Constructor.Companion.zero

/**
 * This object contains common expressions in lambda calculus
 */
object CommonExpressions {
    val id = Lambda("x", Var("x"))
    val K = Lambda("x", Lambda("y", Var("x")))
    val K2 = Lambda("x", Lambda("y", Var("y")))
    val omega = Lambda("y", Application(Var ("y"), Var("y")))
    val omegaBig = Application(omega, omega)

    fun lamChurch(n : Int) : Expr {
        val x = {t : Expr -> Application(Var("s"), t) }
        var body : Expr = Var("z")
        repeat (n) {
            body = x(body)
        }
        return Lambda("s", Lambda("z", body))
    }
    val lamChurchZ = lamChurch(0)
    fun lamChurchSuc(ch : Expr) = Lambda("s", Lambda("z", Application(Application(ch, Var("s")), Application(Var("s"), Var("z")))))

    fun <T : Expr> listFrom(vals : List<T>) : Constructor {
        var core = nil
        for (x in vals.reversed()) {
            core = x.cons(core)
        }
        return core
    }
    val list_xyz = listFrom(listOf("x", "y", "z").map { Var(it) })
    val list_empty = "x".let { x ->
        makeCase(
            Var(x),
            makePattern("Cons", "x", "xs") to lamChurchZ,
                makePattern("Nil") to lamChurchZ
        ).abs(x)
    }.toProgram()
    val list_size_lambdaChurch =
        "x".let { x ->
            Let("list_size",
                makeCase(
                    Var(x),
                        makePattern("Cons", "x", "xs") to lamChurchSuc(Function("list_size").app(Var("xs"))),
                        makePattern("Nil") to lamChurchZ
                ).abs(x), Function("list_size")
            )
    }.toProgram()
    val list_size =
        "x".let { x ->
            Let("list_size",
                makeCase(
                    Var(x),
                    makePattern("Cons", "x", "xs") to Function("list_size").app(Var("xs")).succ(),
                    makePattern("Nil") to zero
                ).abs(x), Function("list_size")
            )
        }.toProgram()

    // program example
    fun sumSquaresN(n : Int) {
        val sum = {
            val vars = listOf("x", "xs", "a")
            val (x, xs, a) = vars
            val (vx, vxs, va) = vars.map { Var(it) }
            makeCase(vxs, makePattern("Nil") to va
                       , makePattern("Cons", x, xs) to (vx plus Function("sum").app(vxs).app(va)) )
                .abs(a).abs(xs)
        }

        val squares = {
            val vars = listOf("x", "xs")
            val (x, xs) = vars
            val (vx, vxs) = vars.map { Var(it) }
            makeCase(vxs, makePattern("Nil") to nil,
                        makePattern("Cons", x, xs) to (vx mult vx).cons(Function("squares").app(vxs)))
        }

        val upto = {
            val vars = listOf("m", "n")
            val (m, n) = vars
            val (vm, vn) = vars.map { Var(it) }
        }
    }

    /* Church numerals arithmetics */
    object Num {
        val sumFname = "+"
        val mulFname = "*"
        fun letSum(wrapped: Expr) : Let {
            val x = "x"
            val y = "y"
            val (pzero, _) = zero.toPattern()
            val (psuc, nvsuc) = zero.succ().toPattern()
            return Let(sumFname,
                makeCase(Var(x),
                    pzero to Var(y),
                    psuc to Function(sumFname).app(Var(nvsuc[0])).app(Var(y).succ())
                ).abs(y).abs(x), wrapped
            )
        }

        fun letMul(wrapped: Expr) : Let {
            val x = "x"
            val y = "y"
            val (pzero, _) = zero.toPattern()
            val (psuc, nvsuc) = zero.succ().toPattern()
            return Let(mulFname,
                makeCase(Var(x),
                pzero to zero,
                    psuc to makeCase(Var(y),
                        pzero to zero,
                        psuc to Function(sumFname).app(Var(x)).app(Function(mulFname).app(Var(x)).app(Var(nvsuc[0])))
                ),
                ).abs(x).abs(y), wrapped
            )
        }

        infix fun Expr.plus(other : Expr) = Function(sumFname).app(this).app(other)
        infix fun Expr.mult(other : Expr) = Function(mulFname).app(this).app(other)
    }
}