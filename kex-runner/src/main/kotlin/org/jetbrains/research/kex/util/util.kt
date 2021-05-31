package org.jetbrains.research.kex.util

import org.jetbrains.research.kthelper.assert.unreachable
import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kfg.ir.Method

private val dot by lazy { kexConfig.getStringValue("view", "dot") ?: unreachable { log.error("Could not find dot") } }
private val viewer by lazy { kexConfig.getStringValue("view", "viewer") ?: unreachable { log.error("Could not find viewer") } }

fun Method.view() = this.view(dot, viewer)