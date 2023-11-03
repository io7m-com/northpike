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
import com.io7m.northpike.agent.internal.console.NPACCommandExecutorType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorFactoryType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceFactoryType;

/**
 * Continuous integration (Agent)
 */

module com.io7m.northpike.agent
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires com.io7m.northpike.agent.api;
  requires com.io7m.northpike.agent.database.api;
  requires com.io7m.northpike.agent.workexec.api;
  requires com.io7m.northpike.connections;
  requires com.io7m.northpike.model;
  requires com.io7m.northpike.protocol.agent.cb;
  requires com.io7m.northpike.protocol.agent;
  requires com.io7m.northpike.protocol.agent_console.cb;
  requires com.io7m.northpike.protocol.agent_console;
  requires com.io7m.northpike.protocol.intro.cb;
  requires com.io7m.northpike.protocol.intro;
  requires com.io7m.northpike.strings;
  requires com.io7m.northpike.telemetry.api;
  requires com.io7m.northpike.tls;

  requires com.io7m.genevan.core;
  requires com.io7m.jmulticlose.core;
  requires com.io7m.repetoir.core;
  requires io.opentelemetry.api;
  requires org.slf4j;

  uses NPAgentDatabaseFactoryType;
  uses NPTelemetryServiceFactoryType;
  uses NPACCommandExecutorType;
  uses NPAWorkExecutorFactoryType;

  provides NPACCommandExecutorType with
    com.io7m.northpike.agent.internal.console.NPACCmdAgentCreate,
    com.io7m.northpike.agent.internal.console.NPACCmdAgentDelete,
    com.io7m.northpike.agent.internal.console.NPACCmdAgentGet,
    com.io7m.northpike.agent.internal.console.NPACCmdAgentList,
    com.io7m.northpike.agent.internal.console.NPACCmdLogin,
    com.io7m.northpike.agent.internal.console.NPACCmdServerDelete,
    com.io7m.northpike.agent.internal.console.NPACCmdServerGet,
    com.io7m.northpike.agent.internal.console.NPACCmdServerList,
    com.io7m.northpike.agent.internal.console.NPACCmdServerPut,
    com.io7m.northpike.agent.internal.console.NPACCmdWorkExecGet,
    com.io7m.northpike.agent.internal.console.NPACCmdWorkExecPut
    ;

  exports com.io7m.northpike.agent;

  exports com.io7m.northpike.agent.internal
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.agent.internal.connection
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.agent.internal.console
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.agent.internal.worker
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.agent.internal.supervisor
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.agent.internal.events
    to com.io7m.northpike.tests;
}
