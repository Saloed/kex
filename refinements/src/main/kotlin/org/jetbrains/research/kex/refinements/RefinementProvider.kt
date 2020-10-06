package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kfg.ir.Method

interface RefinementProvider {
    fun findRefinement(method: Method): Refinements
}
