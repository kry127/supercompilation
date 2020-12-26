package ru.itmo.mit.supercompiler.ast

object Expressions {
    val id = Lambda("x", Var("x"))
    val K = Lambda("x", Lambda("y", Var("x")))
    val K2 = Lambda("x", Lambda("y", Var("y")))
    val omega = Lambda("y", Application(Var ("y"), Var("y")))
    val omegaBig = Application(omega, omega)

    fun church(n : Int) : Expr {
        val x = {t : Expr -> Application(Var("s"), t)}
        var body : Expr = Var("z")
        repeat (n) {
            body = x(body)
        }
        return Lambda("s", Lambda("z", body))
    }
    val churchZ = church(0)
    fun churchSuc(ch : Expr) = Lambda("s", Lambda("z", Application(Application(ch, Var("s")), Application(Var("s"), Var("z")))))

    fun <T : Expr> listFrom(vals : List<T>) : Constructor {
        var core = nil
        for (x in vals.reversed()) {
            core = x.cons(core)
        }
        return core
    }
    val list_xyz = listFrom(listOf("x", "y", "z").map {Var(it)})
    val list_empty = "x".let { x ->
        makeCase(
            Var(x),
            makePattern("Cons", "x", "xs") to churchZ,
                makePattern("Nil") to churchZ
        ).abs(x)
    }
    val list_size =
        "x".let { x ->
            Let("list_size",
        makeCase(
            Var(x),
                makePattern("Cons", "x", "xs") to churchSuc(Function("list_size").app(Var("xs"))),
                makePattern("Nil") to churchZ
        ).abs(x), Function("list_size"))
    }.toProgram()
}