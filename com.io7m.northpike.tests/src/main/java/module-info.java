/*
 * Copyright © 2023 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

import com.io7m.northpike.plans.compiler.NPPlanCompilerFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanSerializerFactoryType;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryFactoryType;
import com.io7m.northpike.server.internal.agents.NPAgentCommandExecutorType;
import com.io7m.northpike.server.internal.users.NPUserCommandExecutorType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceFactoryType;
import com.io7m.northpike.toolexec.api.NPTEvaluationLanguageProviderType;
import com.io7m.northpike.tools.api.NPToolFactoryType;
import net.jqwik.api.providers.ArbitraryProvider;

/**
 * Continuous integration (Test suite)
 */

open module com.io7m.northpike.tests
{
  requires static org.osgi.annotation.versioning;
  requires static org.osgi.annotation.bundle;

  uses ArbitraryProvider;
  uses NPAgentCommandExecutorType;
  uses NPPlanCompilerFactoryType;
  uses NPPlanParserFactoryType;
  uses NPPlanSerializerFactoryType;
  uses NPSCMRepositoryFactoryType;
  uses NPTEvaluationLanguageProviderType;
  uses NPTelemetryServiceFactoryType;
  uses NPToolFactoryType;
  uses NPUserCommandExecutorType;

  requires com.io7m.northpike.agent.api;
  requires com.io7m.northpike.agent.configuration;
  requires com.io7m.northpike.agent.console_client.api;
  requires com.io7m.northpike.agent.console_client;
  requires com.io7m.northpike.agent.database.api;
  requires com.io7m.northpike.agent.database.sqlite;
  requires com.io7m.northpike.agent.locks;
  requires com.io7m.northpike.agent.main;
  requires com.io7m.northpike.agent.metrics;
  requires com.io7m.northpike.agent.workexec.api;
  requires com.io7m.northpike.agent.workexec.local;
  requires com.io7m.northpike.agent.workexec.main;
  requires com.io7m.northpike.agent.workexec.podman;
  requires com.io7m.northpike.agent;
  requires com.io7m.northpike.clock;
  requires com.io7m.northpike.connections;
  requires com.io7m.northpike.database.api;
  requires com.io7m.northpike.database.postgres;
  requires com.io7m.northpike.keys;
  requires com.io7m.northpike.model;
  requires com.io7m.northpike.plans.compiler;
  requires com.io7m.northpike.plans.parsers;
  requires com.io7m.northpike.plans;
  requires com.io7m.northpike.preferences.api;
  requires com.io7m.northpike.preferences.basic;
  requires com.io7m.northpike.protocol.agent.cb;
  requires com.io7m.northpike.protocol.agent;
  requires com.io7m.northpike.protocol.agent_console.cb;
  requires com.io7m.northpike.protocol.agent_console;
  requires com.io7m.northpike.protocol.api;
  requires com.io7m.northpike.protocol.intro.cb;
  requires com.io7m.northpike.protocol.intro;
  requires com.io7m.northpike.protocol.user.cb;
  requires com.io7m.northpike.protocol.user;
  requires com.io7m.northpike.scm_repository.jgit;
  requires com.io7m.northpike.scm_repository.spi;
  requires com.io7m.northpike.server.api;
  requires com.io7m.northpike.server.configuration;
  requires com.io7m.northpike.server.main;
  requires com.io7m.northpike.server;
  requires com.io7m.northpike.shell.commons;
  requires com.io7m.northpike.shell;
  requires com.io7m.northpike.strings;
  requires com.io7m.northpike.telemetry.api;
  requires com.io7m.northpike.tests.arbitraries;
  requires com.io7m.northpike.tls;
  requires com.io7m.northpike.toolexec.api;
  requires com.io7m.northpike.toolexec.js;
  requires com.io7m.northpike.toolexec.program.api;
  requires com.io7m.northpike.tools.api;
  requires com.io7m.northpike.tools.maven;
  requires com.io7m.northpike.user_client.api;
  requires com.io7m.northpike.user_client;

  requires com.googlecode.javaewah;
  requires com.io7m.anethum.api;
  requires com.io7m.anethum.slf4j;
  requires com.io7m.blackthorne.core;
  requires com.io7m.blackthorne.jxe;
  requires com.io7m.cedarbridge.runtime.api;
  requires com.io7m.cedarbridge.runtime.bssio;
  requires com.io7m.cedarbridge.runtime.convenience;
  requires com.io7m.cedarbridge.runtime.time;
  requires com.io7m.ervilla.api;
  requires com.io7m.ervilla.native_exec;
  requires com.io7m.ervilla.postgres;
  requires com.io7m.ervilla.test_extension;
  requires com.io7m.idstore.admin_client.api;
  requires com.io7m.idstore.admin_client;
  requires com.io7m.idstore.protocol.admin;
  requires com.io7m.idstore.server.api;
  requires com.io7m.idstore.server.service.configuration;
  requires com.io7m.idstore.tls;
  requires com.io7m.idstore.user_client.api;
  requires com.io7m.jattribute.core;
  requires com.io7m.jbssio.vanilla;
  requires com.io7m.jmulticlose.core;
  requires com.io7m.junreachable.core;
  requires com.io7m.medrina.api;
  requires com.io7m.northpike.agent.shell;
  requires com.io7m.percentpass.extension;
  requires com.io7m.quarrel.core;
  requires com.io7m.quarrel.ext.xstructural;
  requires com.io7m.quixote.core;
  requires com.io7m.quixote.xml;
  requires com.io7m.repetoir.core;
  requires com.io7m.verdant.core.cb;
  requires com.io7m.verdant.core;
  requires com.io7m.verona.core;
  requires com.io7m.zelador.test_extension;
  requires io.github.classgraph;
  requires io.opentelemetry.api;
  requires java.net.http;
  requires java.sql;
  requires java.xml;
  requires jul.to.slf4j;
  requires net.bytebuddy.agent;
  requires net.bytebuddy;
  requires net.jqwik.api;
  requires org.apache.commons.compress;
  requires org.apache.commons.io;
  requires org.apache.commons.lang3;
  requires org.apache.commons.text;
  requires org.bouncycastle.pg;
  requires org.eclipse.jgit;
  requires org.graalvm.js;
  requires org.graalvm.polyglot;
  requires org.graalvm.truffle.compiler;
  requires org.graalvm.truffle.runtime;
  requires org.graalvm.truffle;
  requires org.jgrapht.core;
  requires org.jline;
  requires org.mockito;
  requires org.postgresql.jdbc;
  requires org.slf4j;
  requires org.xerial.sqlitejdbc;

  requires org.junit.jupiter.api;
  requires org.junit.jupiter.engine;
  requires org.junit.platform.commons;
  requires org.junit.platform.engine;
  requires org.junit.platform.launcher;
}
