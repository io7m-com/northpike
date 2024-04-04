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

import com.io7m.northpike.agent.database.api.NPAgentDatabaseFactoryType;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType;

/**
 * Continuous integration (Agent SQLite database)
 */

module com.io7m.northpike.agent.database.sqlite
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires com.io7m.northpike.agent.database.api;
  requires com.io7m.northpike.agent.workexec.api;
  requires com.io7m.northpike.model;
  requires com.io7m.northpike.strings;
  requires com.io7m.northpike.telemetry.api;

  requires com.io7m.cedarbridge.runtime.api;
  requires com.io7m.cedarbridge.runtime.bssio;
  requires com.io7m.cedarbridge.runtime.convenience;
  requires com.io7m.jmulticlose.core;
  requires com.io7m.trasco.api;
  requires com.io7m.trasco.vanilla;
  requires io.opentelemetry.api;
  requires io.opentelemetry.context;
  requires io.opentelemetry.semconv;
  requires org.jooq;
  requires org.slf4j;
  requires org.xerial.sqlitejdbc;
  requires com.io7m.jbssio.vanilla;

  uses NPASQueryProviderType;

  provides NPAgentDatabaseFactoryType
    with com.io7m.northpike.agent.database.sqlite.NPASDatabases;

  provides NPASQueryProviderType with
    com.io7m.northpike.agent.database.sqlite.internal.NPASAgentDelete,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAgentGet,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAgentList,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAgentPut,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAgentServerAssign,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAgentServerGet,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAgentServerUnassign,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAgentWorkExecGet,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAgentWorkExecPut,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAssignmentLogDelete,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAssignmentLogGet,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAssignmentLogList,
    com.io7m.northpike.agent.database.sqlite.internal.NPASAssignmentLogPut,
    com.io7m.northpike.agent.database.sqlite.internal.NPASServerDelete,
    com.io7m.northpike.agent.database.sqlite.internal.NPASServerGet,
    com.io7m.northpike.agent.database.sqlite.internal.NPASServerList,
    com.io7m.northpike.agent.database.sqlite.internal.NPASServerPut
    ;

  exports com.io7m.northpike.agent.database.sqlite;
}
