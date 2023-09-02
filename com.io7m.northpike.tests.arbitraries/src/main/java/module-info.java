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

open module com.io7m.northpike.tests.arbitraries
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires net.jqwik.api;
  requires com.io7m.jlexing.core;

  requires com.io7m.northpike.model;
  requires com.io7m.northpike.protocol.agent;
  requires com.io7m.northpike.protocol.intro;
  requires com.io7m.northpike.toolexec;

  uses ArbitraryProvider;

  provides ArbitraryProvider with
    com.io7m.northpike.tests.arbitraries.NPArbAgentLabel,
    com.io7m.northpike.tests.arbitraries.NPArbAgentLabelMatch,
    com.io7m.northpike.tests.arbitraries.NPArbAgentResourceName,
    com.io7m.northpike.tests.arbitraries.NPArbAgentWorkItem,
    com.io7m.northpike.tests.arbitraries.NPArbCommit,
    com.io7m.northpike.tests.arbitraries.NPArbCommitAuthor,
    com.io7m.northpike.tests.arbitraries.NPArbCommitID,
    com.io7m.northpike.tests.arbitraries.NPArbDottedName,
    com.io7m.northpike.tests.arbitraries.NPArbErrorCode,
    com.io7m.northpike.tests.arbitraries.NPArbFormatName,
    com.io7m.northpike.tests.arbitraries.NPArbKey,
    com.io7m.northpike.tests.arbitraries.NPArbLexicalPosition,
    com.io7m.northpike.tests.arbitraries.NPArbOffsetDateTime,
    com.io7m.northpike.tests.arbitraries.NPArbRepository,
    com.io7m.northpike.tests.arbitraries.NPArbSCMProviderDescription,
    com.io7m.northpike.tests.arbitraries.NPArbTimeRange,
    com.io7m.northpike.tests.arbitraries.NPArbToolExecutionEvaluated,
    com.io7m.northpike.tests.arbitraries.NPArbToolExecutionIdentifier,
    com.io7m.northpike.tests.arbitraries.NPArbToolExecutionName,
    com.io7m.northpike.tests.arbitraries.NPArbToolName,
    com.io7m.northpike.tests.arbitraries.NPArbToolReference,
    com.io7m.northpike.tests.arbitraries.NPArbToolReferenceName,
    com.io7m.northpike.tests.arbitraries.NPArbVersion,
    com.io7m.northpike.tests.arbitraries.NPArbWorkItemIdentifier,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandCDisconnect,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandCEnvironmentInfo,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandCLogin,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandCWorkItemFailed,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandCWorkItemOutput,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandCWorkItemStarted,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandCWorkItemSucceeded,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandSLatencyCheck,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandSWorkOffered,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandSWorkSent,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbAMessage,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbAResponseError,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbAResponseOK,
    com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbAResponseSLatencyCheck,
    com.io7m.northpike.tests.arbitraries.protocol.intro.NPArbIError,
    com.io7m.northpike.tests.arbitraries.protocol.intro.NPArbIMessage,
    com.io7m.northpike.tests.arbitraries.protocol.intro.NPArbIProtocol,
    com.io7m.northpike.tests.arbitraries.protocol.intro.NPArbIProtocolsAvailable,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbDescription,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbEAnd,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbEFalse,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbEIsEqual,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbENot,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbENumber,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbEOr,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbEString,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbEStringSetContains,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbETrue,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbEVariableBoolean,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbEVariableNumber,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbEVariableString,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbEVariableStringSet,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbExpressionType,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbPlanVariable,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbPlanVariableBoolean,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbPlanVariableNumeric,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbPlanVariableString,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbPlanVariables,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbSArgumentAdd,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbSComment,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbSEnvironmentClear,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbSEnvironmentPass,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbSEnvironmentRemove,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbSEnvironmentSet,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbSIf,
    com.io7m.northpike.tests.arbitraries.toolexec.NPArbStatementType
    ;

  exports com.io7m.northpike.tests.arbitraries;
  exports com.io7m.northpike.tests.arbitraries.protocol.agent;
  exports com.io7m.northpike.tests.arbitraries.protocol.intro;
}
