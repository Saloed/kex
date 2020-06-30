package org.jetbrains.research.kex.test.refinements

import java.io.File
import java.net.Socket
import java.nio.ByteBuffer
import java.nio.channels.AsynchronousFileChannel
import java.nio.channels.Channel
import java.util.concurrent.Future

object Inlining {
    fun deepInlining(a: Int): Int {
        val res = inlineLvl1(a)
        if (res == 0) throw IllegalArgumentException("Zero")
        return res
    }

    private fun inlineLvl1(x: Int): Int {
        return inlineLvl2(x + 1) + 1
    }

    private fun inlineLvl2(x: Int): Int {
        return inlineLvl3(x + 2) + 2
    }

    private fun inlineLvl3(x: Int): Int {
        if (x < 0) throw IllegalArgumentException("Below zero")
        return x + 3
    }

    class Failer {
        fun exceptionSource(a: Int): Nothing {
            throw IllegalStateException("failed")
        }
    }

    fun inlineExceptionSource(f: Failer, x: Int): Nothing {
        var a = 17
        if (x != 0) {
            a += 5
        }
        f.exceptionSource(a)
    }

}