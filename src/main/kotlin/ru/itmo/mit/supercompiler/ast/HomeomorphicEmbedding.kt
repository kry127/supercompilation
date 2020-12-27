package ru.itmo.mit.supercompiler.ast


class BoundedVariables (
    val arrow: Map<String, String?> = mapOf(),
    val coarrow: Map<String, String?> = mapOf()
) {
    val domain
        get() = arrow.keys
    val codomain
        get() = coarrow.keys

    fun inDomain(e : String) : Boolean = e in arrow
    fun inCodomain(e : String) : Boolean = e in coarrow
    fun has(p : Pair<String, String>) : Boolean = arrow[p.first] == p.second && coarrow[p.second] == p.first


    fun put(p : Pair<String, String>) = BoundedVariables(arrow + p, coarrow + (p.second to p.first))
    fun putDomain(v : String) = BoundedVariables(arrow + (v to null), coarrow - v)
    fun putCodomain(v : String) = BoundedVariables(arrow, coarrow + (v to null))

    fun putCodomain(v : List<String>) = BoundedVariables(arrow, coarrow + (v.map {it to null}))
}

/**
 * This function defines homeomorphic embedding. This expression tells, that
 * this expression embeds into other exception
 */
private infix fun Expr.homo(other : Expr) = homo(BoundedVariables(), other)
private infix fun Expr.variableHomo(other : Expr) = variableHomo(BoundedVariables(), other)
private infix fun Expr.divingHomo(other : Expr) = divingHomo(BoundedVariables(), other)

/**
 * This function defines coupling embedding -- a partial type of embedding
 * which tells us that expressions are at least lambda, constructor,
 * application, or case expression at the top level
 */
private infix fun Expr.couplingHomo(other : Expr) = couplingHomo(BoundedVariables(), other)

private fun Expr.homo(ctx : BoundedVariables, other : Expr) =
    variableHomo(ctx, other) || couplingHomo(ctx, other) || divingHomo(ctx, other)


private fun Expr.variableHomo(ctx : BoundedVariables, other : Expr) : Boolean {
    if (this is Function && other is Function) return this.name == other.name
    if (this is Var && other is Var) {
        if (ctx.has(name to other.name)) return true
        if (ctx.inDomain(name) || ctx.inCodomain(other.name)) return false
        return true
    }
    return false
}

private fun Expr.divingHomo(ctx : BoundedVariables, other : Expr) : Boolean {
    // TODO don't understand why, but article says it is a good move.
    // Example : \x.\y.f  <=>   \x.\y.x f
    if (!(freeVars intersect ctx.domain).isEmpty()) return false
    return when (other) {
        is Constructor -> other.args.any { homo(ctx, it) }
        is Lambda -> homo(ctx.putCodomain(other.name), other.body)
        is Application -> homo(ctx, other.lhs) || homo(ctx, other.rhs)
        is Case -> homo(ctx, other.match) ||
                other.branches.any { (pt, body) ->
                    homo(ctx.putCodomain(pt.args.map{it.name}), body)
                }
        else -> false
    }
}

private fun Expr.couplingHomo(ctx : BoundedVariables, other : Expr) : Boolean {
    if (this is Constructor && other is Constructor && name == other.name) {
        return args.zip(other.args).all {(l, r) -> l.homo(ctx, r)}
    } else if (this is Lambda && other is Lambda) {
        return body.homo(ctx.put(name to other.name), other.body)
    } else if (this is Application && other is Application) {
        // left should not be application === left is checking with coupling, right with ordinary homo
        return lhs.couplingHomo(ctx, other.lhs) && rhs.homo(other.rhs)
    } else if (this is Case && other is Case) {
        return match.homo(ctx, other.match) &&
                other.branches.all { (pt, body) ->
                    homo(ctx.putCodomain(pt.args.map{it.name}), body)
                }
    }
    return false
}