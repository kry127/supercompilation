package ru.itmo.mit.supercompiler

import ru.itmo.mit.supercompiler.Constructor.Companion.cons
import ru.itmo.mit.supercompiler.Constructor.Companion.nil
import ru.itmo.mit.supercompiler.Constructor.Companion.num
import ru.itmo.mit.supercompiler.Constructor.Companion.succ
import ru.itmo.mit.supercompiler.Constructor.Companion.zero
import ru.itmo.mit.supercompiler.Function.Companion.leq
import ru.itmo.mit.supercompiler.Function.Companion.mulFname
import ru.itmo.mit.supercompiler.Function.Companion.mult
import ru.itmo.mit.supercompiler.Function.Companion.plus
import ru.itmo.mit.supercompiler.Function.Companion.sumFname
import ru.itmo.mit.supercompiler.Pattern.Companion.patFalse
import ru.itmo.mit.supercompiler.Pattern.Companion.patSuc
import ru.itmo.mit.supercompiler.Pattern.Companion.patTrue
import ru.itmo.mit.supercompiler.Pattern.Companion.patZero

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
    fun sumSquaresN(N : Expr) : Program {

        val fnames = listOf("sum", "squares", "upto")
        val funcRefs = fnames.map { Function(it) }
        val (fSum, fSquares, fUpto) = funcRefs

        val sum = {
            val vars = listOf("x", "xs", "a")
            val (x, xs, a) = vars
            val (vx, vxs, va) = vars.map { Var(it) }
            listOf(xs, a) arrow makeCase(vxs,
                makePattern("Nil") to va,
                   makePattern("Cons", x, xs) to (fSum app vxs app (vx plus va))
            )
        }

        val squares = {
            val vars = listOf("x", "xs")
            val (x, xs) = vars
            val (vx, vxs) = vars.map { Var(it) }
            listOf(xs) arrow makeCase(vxs,
                makePattern("Nil") to nil,
                    makePattern("Cons", x, xs) to (vx mult vx).cons(fSquares app vxs)
            )
        }

        val upto = {
            val vars = listOf("m", "n")
            val (m, n) = vars
            val (vm, vn) = vars.map { Var(it) }
            listOf(m, n) arrow makeCase(vn leq vm,
                patTrue to nil,
                patFalse to (vm cons (fUpto app (vm plus num(1)) app vn))
            )
        }

        val funcDefs = listOf(sum(), squares(), upto())
        val expr = fSum app (fSquares app (fUpto app num(1) app N)) app zero
        return Program.convertToProgram(expr, fnames.zip(funcDefs).toMap())
    }

    /* Church numerals arithmetics */
    object Num {
        fun letSum(wrapped: Expr) : Let {
            val x = "x"
            val y = "y"
            return Let(sumFname,
                makeCase(Var(x),
                    patZero to Var(y),
                    patSuc(x) to Function(sumFname).app(Var(x)).app(Var(y).succ())
                ).abs(y).abs(x), wrapped
            )
        }

        fun letMul(wrapped: Expr) : Let {
            val x = "x"
            val y = "y"
            return Let(mulFname,
                listOf(x, y) arrow makeCase(Var(x),
                patZero to zero,
                    patSuc("tmp") to makeCase(Var(y),
                        patZero to zero,
                        patSuc(y) to (Var(x) plus (Var(x) mult Var(y)))
                ),
                ), wrapped)
        }
    }
}