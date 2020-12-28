package ru.itmo.mit.supercompiler


typealias Substitution = Map<String, Expr>

/**
 * Applies substitution to the expression
 * Yields IllegalStateException when domain of subsitution intersects with bound variables
 */
fun Expr.applySub(sub : Substitution) : Expr {
    if (!(sub.keys intersect this.boundVars).isEmpty()) {
        error("Illegal substitution: collision of domain and bound variables")
    }
    return applySub0(sub)
}

private fun Expr.applySub0(sub : Substitution) : Expr {
    return when(this) {
        is Var -> sub[name] ?: this
        is Constructor -> Constructor(name, args.map { it.applySub0(sub) })
        is Function -> this
        is Lambda -> Lambda(name, body.applySub0(sub))
        is Application -> Application(lhs.applySub0(sub), rhs.applySub0(sub))
        is Case -> Case(match.applySub0(sub), branches.map { (p, e) -> p to e.applySub0(sub) })
        is Let -> Let(name, definition.applySub0(sub), body.applySub0(sub))
    }
}