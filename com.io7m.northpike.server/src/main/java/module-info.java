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

import com.io7m.northpike.server.internal.telemetry.NPTelemetryServices;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceFactoryType;

/**
 * Continuous integration (Server)
 */

module com.io7m.northpike.server
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires com.io7m.northpike.connections;
  requires com.io7m.northpike.database.api;
  requires com.io7m.northpike.model;
  requires com.io7m.northpike.protocol.agent.cb;
  requires com.io7m.northpike.protocol.agent;
  requires com.io7m.northpike.protocol.intro.cb;
  requires com.io7m.northpike.protocol.intro;
  requires com.io7m.northpike.scm_repository.spi;
  requires com.io7m.northpike.server.api;
  requires com.io7m.northpike.strings;
  requires com.io7m.northpike.telemetry.api;
  requires com.io7m.northpike.tls;

  requires com.io7m.anethum.api;
  requires com.io7m.anethum.slf4j;
  requires com.io7m.jmulticlose.core;
  requires com.io7m.medrina.vanilla;
  requires com.io7m.repetoir.core;
  requires io.opentelemetry.api;
  requires io.opentelemetry.context;
  requires io.opentelemetry.exporter.otlp;
  requires io.opentelemetry.sdk.common;
  requires io.opentelemetry.sdk.logs;
  requires io.opentelemetry.sdk.metrics;
  requires io.opentelemetry.sdk.trace;
  requires io.opentelemetry.sdk;
  requires io.opentelemetry.semconv;
  requires org.eclipse.jetty.server;
  requires org.slf4j;

  uses NPTelemetryServiceFactoryType;

  provides NPTelemetryServiceFactoryType
    with NPTelemetryServices;

  exports com.io7m.northpike.server;

  exports com.io7m.northpike.server.internal.archives
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.telemetry
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.agents
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.repositories
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.configuration
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.clock
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.events
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.metrics
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal
    to com.io7m.northpike.tests;
}