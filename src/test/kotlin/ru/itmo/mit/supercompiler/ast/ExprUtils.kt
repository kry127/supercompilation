package ru.itmo.mit.supercompiler.ast


// this is a test from homeomorphic embedding article:
// https://pat.keldysh.ru/~ilya/preprints/HoscInternals_ru.pdf
fun makeArticleCases(a : Expr, b : Expr) = makeCase(Var("x"), makePattern("Z") to Var("x"),
    makePattern("S", "b") to (a app b))