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


package com.io7m.northpike.shell.commons;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorContainerImage;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPRepositoryCredentialsType;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionIdentifierSet;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import com.io7m.northpike.model.agents.NPAgentLabelSet;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanName;
import com.io7m.northpike.model.security.NPRoleSet;
import com.io7m.northpike.model.tls.NPTLSConfigurationKind;
import com.io7m.quarrel.core.QValueConverterDirectory;
import com.io7m.quarrel.core.QValueConverterDirectoryType;

/**
 * Value converters for the shell commands.
 */

public final class NPShellValueConverters
{
  private static final QValueConverterDirectoryType CONVERTERS =
    QValueConverterDirectory.core()
      .with(
        NPAWorkExecutorContainerImage.class,
        new NPAWorkExecContainerImageConverter())
      .with(
        NPAWorkExecName.class,
        new NPAWorkExecNameConverter())
      .with(
        NPAssignmentName.class,
        new NPAssignmentNameConverter())
      .with(
        NPRepositoryID.class,
        new NPRepositoryIDConverter())
      .with(
        NPAgentServerID.class,
        new NPAgentServerIDConverter())
      .with(
        NPAgentID.class,
        new NPAgentIDConverter())
      .with(
        NPAgentKeyPublicType.class,
        new NPAgentPublicKeyConverter())
      .with(
        RDottedName.class,
        new RDottedNameConverter())
      .with(
        NPAgentLocalName.class,
        new NPAgentLocalNameConverter())
      .with(
        NPAgentLabelName.class,
        new NPAgentLabelNameConverter())
      .with(
        NPFormatName.class,
        new NPFormatNameConverter())
      .with(
        NPToolExecutionName.class,
        new NPToolExecutionNameConverter())
      .with(
        NPToolExecutionIdentifier.class,
        new NPToolExecutionIdentifierConverter())
      .with(
        NPPlanIdentifier.class,
        new NPPlanIdentifierConverter())
      .with(
        NPToolExecutionIdentifierSet.class,
        new NPToolExecutionIdentifierSetConverter())
      .with(
        NPToolName.class,
        new NPToolNameConverter())
      .with(
        NPPlanName.class,
        new NPPlanNameConverter())
      .with(
        NPRepositoryCredentialsType.class,
        new NPRepositoryCredentialsConverter())
      .with(
        NPFingerprint.class,
        new NPFingerprintConverter())
      .with(
        NPRoleSet.class,
        new NPRoleSetConverter())
      .with(
        NPTLSConfigurationKind.class,
        new NPTLSConfigurationKindConverter())
      .with(
        NPAgentLabelSet.class,
        new NPAgentLabelSetConverter())
      .with(
        NPCommitUnqualifiedID.class,
        new NPCommitUnqualifiedIDConverter());

  private NPShellValueConverters()
  {

  }

  /**
   * @return The value converters
   */

  public static QValueConverterDirectoryType get()
  {
    return CONVERTERS;
  }
}
