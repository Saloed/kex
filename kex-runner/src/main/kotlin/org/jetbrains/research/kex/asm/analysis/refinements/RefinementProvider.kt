package org.jetbrains.research.kex.asm.analysis.refinements

import org.jetbrains.research.kfg.ir.Method

interface RefinementProvider {
    fun findRefinement(method: Method): Refinements
}