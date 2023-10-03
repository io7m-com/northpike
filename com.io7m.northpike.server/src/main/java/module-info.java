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
import com.io7m.northpike.server.internal.telemetry.NPTelemetryServices;
import com.io7m.northpike.server.internal.users.NPUserCommandExecutorType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceFactoryType;
import com.io7m.northpike.toolexec.NPTXParserFactoryType;

/**
 * Continuous integration (Server)
 */

module com.io7m.northpike.server
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires com.io7m.northpike.clock;
  requires com.io7m.northpike.connections;
  requires com.io7m.northpike.database.api;
  requires com.io7m.northpike.keys;
  requires com.io7m.northpike.model;
  requires com.io7m.northpike.plans.compiler;
  requires com.io7m.northpike.plans.parsers;
  requires com.io7m.northpike.plans;
  requires com.io7m.northpike.protocol.agent.cb;
  requires com.io7m.northpike.protocol.agent;
  requires com.io7m.northpike.protocol.intro.cb;
  requires com.io7m.northpike.protocol.intro;
  requires com.io7m.northpike.protocol.user.cb;
  requires com.io7m.northpike.protocol.user;
  requires com.io7m.northpike.scm_repository.spi;
  requires com.io7m.northpike.server.api;
  requires com.io7m.northpike.strings;
  requires com.io7m.northpike.telemetry.api;
  requires com.io7m.northpike.tls;
  requires com.io7m.northpike.toolexec;

  requires com.io7m.anethum.api;
  requires com.io7m.anethum.slf4j;
  requires com.io7m.idstore.user_client.api;
  requires com.io7m.idstore.user_client;
  requires com.io7m.jaffirm.core;
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

  uses NPPlanCompilerFactoryType;
  uses NPPlanParserFactoryType;
  uses NPTXParserFactoryType;
  uses NPTelemetryServiceFactoryType;
  uses NPUserCommandExecutorType;

  provides NPTelemetryServiceFactoryType
    with NPTelemetryServices;

  provides NPUserCommandExecutorType with
    com.io7m.northpike.server.internal.users.NPUCmdAgentGet,
    com.io7m.northpike.server.internal.users.NPUCmdAgentLabelDelete,
    com.io7m.northpike.server.internal.users.NPUCmdAgentLabelGet,
    com.io7m.northpike.server.internal.users.NPUCmdAgentLabelPut,
    com.io7m.northpike.server.internal.users.NPUCmdAgentLabelSearchBegin,
    com.io7m.northpike.server.internal.users.NPUCmdAgentLabelSearchNext,
    com.io7m.northpike.server.internal.users.NPUCmdAgentLabelSearchPrevious,
    com.io7m.northpike.server.internal.users.NPUCmdAgentPut,
    com.io7m.northpike.server.internal.users.NPUCmdAgentSearchBegin,
    com.io7m.northpike.server.internal.users.NPUCmdAgentSearchNext,
    com.io7m.northpike.server.internal.users.NPUCmdAgentSearchPrevious,
    com.io7m.northpike.server.internal.users.NPUCmdAgentsConnected,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentExecute,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentExecutionDelete,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentExecutionSearchBegin,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentExecutionSearchNext,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentExecutionSearchPrevious,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentExecutionWorkItems,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentGet,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentPut,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentSearchBegin,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentSearchNext,
    com.io7m.northpike.server.internal.users.NPUCmdAssignmentSearchPrevious,
    com.io7m.northpike.server.internal.users.NPUCmdAuditSearchBegin,
    com.io7m.northpike.server.internal.users.NPUCmdAuditSearchNext,
    com.io7m.northpike.server.internal.users.NPUCmdAuditSearchPrevious,
    com.io7m.northpike.server.internal.users.NPUCmdDisconnect,
    com.io7m.northpike.server.internal.users.NPUCmdLogin,
    com.io7m.northpike.server.internal.users.NPUCmdPlanDelete,
    com.io7m.northpike.server.internal.users.NPUCmdPlanGet,
    com.io7m.northpike.server.internal.users.NPUCmdPlanPut,
    com.io7m.northpike.server.internal.users.NPUCmdPlanSearchBegin,
    com.io7m.northpike.server.internal.users.NPUCmdPlanSearchNext,
    com.io7m.northpike.server.internal.users.NPUCmdPlanSearchPrevious,
    com.io7m.northpike.server.internal.users.NPUCmdPlanValidate,
    com.io7m.northpike.server.internal.users.NPUCmdPublicKeyDelete,
    com.io7m.northpike.server.internal.users.NPUCmdPublicKeyGet,
    com.io7m.northpike.server.internal.users.NPUCmdPublicKeyPut,
    com.io7m.northpike.server.internal.users.NPUCmdPublicKeySearchBegin,
    com.io7m.northpike.server.internal.users.NPUCmdPublicKeySearchNext,
    com.io7m.northpike.server.internal.users.NPUCmdPublicKeySearchPrevious,
    com.io7m.northpike.server.internal.users.NPUCmdRepositoryGet,
    com.io7m.northpike.server.internal.users.NPUCmdRepositoryPublicKeyAssign,
    com.io7m.northpike.server.internal.users.NPUCmdRepositoryPublicKeyUnassign,
    com.io7m.northpike.server.internal.users.NPUCmdRepositoryPublicKeysAssigned,
    com.io7m.northpike.server.internal.users.NPUCmdRepositoryPut,
    com.io7m.northpike.server.internal.users.NPUCmdRepositorySearchBegin,
    com.io7m.northpike.server.internal.users.NPUCmdRepositorySearchNext,
    com.io7m.northpike.server.internal.users.NPUCmdRepositorySearchPrevious,
    com.io7m.northpike.server.internal.users.NPUCmdRolesAssign,
    com.io7m.northpike.server.internal.users.NPUCmdRolesGet,
    com.io7m.northpike.server.internal.users.NPUCmdRolesRevoke,
    com.io7m.northpike.server.internal.users.NPUCmdSCMProvidersSupported,
    com.io7m.northpike.server.internal.users.NPUCmdSelf,
    com.io7m.northpike.server.internal.users.NPUCmdToolExecutionDescriptionGet,
    com.io7m.northpike.server.internal.users.NPUCmdToolExecutionDescriptionPut,
    com.io7m.northpike.server.internal.users.NPUCmdToolExecutionDescriptionSearchBegin,
    com.io7m.northpike.server.internal.users.NPUCmdToolExecutionDescriptionSearchNext,
    com.io7m.northpike.server.internal.users.NPUCmdToolExecutionDescriptionSearchPrevious,
    com.io7m.northpike.server.internal.users.NPUCmdToolExecutionDescriptionValidate,
    com.io7m.northpike.server.internal.users.NPUCmdUserSearchBegin,
    com.io7m.northpike.server.internal.users.NPUCmdUserSearchNext,
    com.io7m.northpike.server.internal.users.NPUCmdUserSearchPrevious,
    com.io7m.northpike.server.internal.users.NPUCmdUsersConnected
    ;

  exports com.io7m.northpike.server;

  exports com.io7m.northpike.server.internal to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.agents to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.archives to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.assignments to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.configuration to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.events to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.metrics to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.repositories to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.security to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.telemetry to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.tls to com.io7m.northpike.tests;
  exports com.io7m.northpike.server.internal.users to com.io7m.northpike.tests;
}