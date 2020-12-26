package ru.itmo.mit.supercompiler.ast

object Generator {
    /*
     * The simplest generator of bound variables
     */
    fun makePostfixNumberSequenceCallback(prefix : String, isValid : (String) -> Boolean = { true }) : Sequence<String> {
        var i = 0
        return generateSequence {
            while (true) {
                if (isValid("$prefix${++i}")) break
            }
            "$prefix$i"
        }
    }

    fun makePostfixNumberSequence(prefix : String, except : Set<String> = emptySet()) : Sequence<String> {
        return makePostfixNumberSequenceCallback(prefix) {!(it in except)}
    }

}