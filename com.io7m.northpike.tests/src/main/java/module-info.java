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

import net.jqwik.api.providers.ArbitraryProvider;

/**
 * Continuous integration (Test suite)
 */

open module com.io7m.northpike.tests
{
  requires static org.osgi.annotation.versioning;
  requires static org.osgi.annotation.bundle;

  uses ArbitraryProvider;

  requires com.io7m.northpike.agent.api;
  requires com.io7m.northpike.agent.configuration;
  requires com.io7m.northpike.agent.expressions;
  requires com.io7m.northpike.agent.main;
  requires com.io7m.northpike.agent;
  requires com.io7m.northpike.assignments;
  requires com.io7m.northpike.database.api;
  requires com.io7m.northpike.database.postgres;
  requires com.io7m.northpike.model;
  requires com.io7m.northpike.plans.compiler;
  requires com.io7m.northpike.plans.parsers;
  requires com.io7m.northpike.plans;
  requires com.io7m.northpike.protocol.agent.cb;
  requires com.io7m.northpike.protocol.agent;
  requires com.io7m.northpike.protocol.api;
  requires com.io7m.northpike.protocol.intro.cb;
  requires com.io7m.northpike.protocol.intro;
  requires com.io7m.northpike.protocol.user.cb;
  requires com.io7m.northpike.protocol.user;
  requires com.io7m.northpike.scm_repository.jgit;
  requires com.io7m.northpike.scm_repository.spi;
  requires com.io7m.northpike.server.api;
  requires com.io7m.northpike.server.configuration;
  requires com.io7m.northpike.server;
  requires com.io7m.northpike.strings;
  requires com.io7m.northpike.telemetry.api;
  requires com.io7m.northpike.tests.arbitraries;
  requires com.io7m.northpike.tls;
  requires com.io7m.northpike.toolexec;
  requires com.io7m.northpike.tools.api;
  requires com.io7m.northpike.tools.maven;
  requires com.io7m.northpike.user_client.api;
  requires com.io7m.northpike.user_client;

  requires com.googlecode.javaewah;
  requires com.io7m.anethum.api;
  requires com.io7m.anethum.slf4j;
  requires com.io7m.blackthorne.core;
  requires com.io7m.blackthorne.jxe;
  requires com.io7m.ervilla.api;
  requires com.io7m.ervilla.native_exec;
  requires com.io7m.ervilla.postgres;
  requires com.io7m.ervilla.test_extension;
  requires com.io7m.idstore.admin_client.api;
  requires com.io7m.idstore.admin_client;
  requires com.io7m.idstore.user_client.api;
  requires com.io7m.jattribute.core;
  requires com.io7m.jmulticlose.core;
  requires com.io7m.junreachable.core;
  requires com.io7m.medrina.api;
  requires com.io7m.percentpass.extension;
  requires com.io7m.quixote.core;
  requires com.io7m.repetoir.core;
  requires com.io7m.verdant.core.cb;
  requires com.io7m.verdant.core;
  requires com.io7m.verona.core;
  requires com.io7m.zelador.test_extension;
  requires io.opentelemetry.api;
  requires java.net.http;
  requires java.sql;
  requires java.xml;
  requires net.bytebuddy.agent;
  requires net.bytebuddy;
  requires net.jqwik.api;
  requires org.apache.commons.compress;
  requires org.apache.commons.io;
  requires org.jgrapht.core;
  requires org.mockito;
  requires org.postgresql.jdbc;
  requires org.slf4j;

  requires transitive org.junit.jupiter.api;
  requires transitive org.junit.jupiter.engine;
  requires transitive org.junit.platform.commons;
  requires transitive org.junit.platform.engine;

  exports com.io7m.northpike.tests.database;
  exports com.io7m.northpike.tests.containers;
  exports com.io7m.northpike.tests.scm_repository;
}
