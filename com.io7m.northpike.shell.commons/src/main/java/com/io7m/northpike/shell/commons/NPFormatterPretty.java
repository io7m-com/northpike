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

import com.io7m.medrina.api.MRoleName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorSummary;
import com.io7m.northpike.model.NPAuditEvent;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPPublicKeySummary;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositorySummary;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.model.NPToolDescription;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionDescriptionSummary;
import com.io7m.northpike.model.NPToolSummary;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.model.agents.NPAgentLabel;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeRecord;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.agents.NPAgentServerSummary;
import com.io7m.northpike.model.agents.NPAgentStatus;
import com.io7m.northpike.model.agents.NPAgentSummary;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.model.plans.NPPlanDescriptionUnparsed;
import com.io7m.northpike.model.plans.NPPlanFormatDescription;
import com.io7m.northpike.model.plans.NPPlanSummary;
import com.io7m.northpike.model.tls.NPTLSConfigurationType;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.model.tls.NPTLSEnabledClientAnonymous;
import com.io7m.northpike.model.tls.NPTLSEnabledExplicit;
import com.io7m.northpike.preferences.api.NPPreferenceServerBookmark;
import com.io7m.northpike.preferences.api.NPPreferenceServerCredentialsType;
import com.io7m.northpike.preferences.api.NPPreferenceServerUsernamePassword;
import com.io7m.tabla.core.TColumnWidthConstraint;
import com.io7m.tabla.core.TTableRendererType;
import com.io7m.tabla.core.TTableType;
import com.io7m.tabla.core.TTableWidthConstraintRange;
import com.io7m.tabla.core.Tabla;
import org.apache.commons.lang3.StringUtils;
import org.jline.terminal.Terminal;

import java.io.PrintWriter;
import java.time.OffsetDateTime;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.UUID;

import static com.io7m.northpike.shell.commons.NPFormatterRaw.formatSchedule;
import static com.io7m.tabla.core.TColumnWidthConstraint.any;
import static com.io7m.tabla.core.TColumnWidthConstraint.atLeastContentOrHeader;
import static com.io7m.tabla.core.TConstraintHardness.SOFT_CONSTRAINT;
import static com.io7m.tabla.core.TTableWidthConstraintType.tableWidthExact;

/**
 * A pretty formatter.
 */

public final class NPFormatterPretty implements NPFormatterType
{
  private final Terminal terminal;
  private final TTableRendererType tableRenderer;

  /**
   * A pretty formatter.
   *
   * @param inTerminal The terminal
   */

  public NPFormatterPretty(
    final Terminal inTerminal)
  {
    this.terminal =
      Objects.requireNonNull(inTerminal, "terminal");
    this.tableRenderer =
      Tabla.framedUnicodeRenderer();
  }

  @Override
  public String toString()
  {
    return "[%s]".formatted(this.getClass().getSimpleName());
  }

  private int width()
  {
    var width = Math.max(0, this.terminal.getWidth());
    if (width == 0) {
      width = 80;
    }
    return width;
  }

  private int widthFor(
    final int columns)
  {
    final var columnPad = 2;
    final var columnEdge = 1;
    return this.width() - (2 + (columns * (columnEdge + columnPad)));
  }

  private TTableWidthConstraintRange softTableWidth(
    final int columns)
  {
    return tableWidthExact(this.widthFor(columns), SOFT_CONSTRAINT);
  }

  @Override
  public void formatAudits(
    final NPPage<NPAuditEvent> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(5))
        .declareColumn("ID", atLeastContentOrHeader())
        .declareColumn("Time", atLeastContentOrHeader())
        .declareColumn("Owner", atLeastContentOrHeader())
        .declareColumn("Type", atLeastContentOrHeader())
        .declareColumn("Data", atLeastContentOrHeader());

    for (final var audit : page.items()) {
      builder.addRow()
        .addCell(Long.toUnsignedString(audit.id()))
        .addCell(audit.time().toString())
        .addCell(audit.owner().toString())
        .addCell(audit.type())
        .addCell(audit.data().toString());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatRepository(
    final NPRepositoryDescription repository)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Attribute", atLeastContentOrHeader())
        .declareColumn("Value", atLeastContentOrHeader());

    builder.addRow()
      .addCell("Repository ID")
      .addCell(repository.id().toString());
    builder.addRow()
      .addCell("SCM Provider")
      .addCell(repository.provider().toString());
    builder.addRow()
      .addCell("URI")
      .addCell(repository.url().toString());
    builder.addRow()
      .addCell("Credentials")
      .addCell(repository.credentials().toString());
    builder.addRow()
      .addCell("Signing Policy")
      .addCell(repository.signingPolicy().toString());

    this.renderTable(builder.build());
  }

  @Override
  public void formatRepositorySummaries(
    final NPPage<NPRepositorySummary> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(3))
        .declareColumn("ID", atLeastContentOrHeader())
        .declareColumn("Provider", atLeastContentOrHeader())
        .declareColumn("URI", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.id().toString())
        .addCell(item.provider().value())
        .addCell(item.url().toString());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatPublicKey(
    final NPPublicKey key)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Attribute", atLeastContentOrHeader())
        .declareColumn("Value", atLeastContentOrHeader());

    builder.addRow()
      .addCell("Fingerprint")
      .addCell(key.fingerprint().value());
    builder.addRow()
      .addCell("Time Created")
      .addCell(key.timeCreated().toString());
    builder.addRow()
      .addCell("Time Expires")
      .addCell(
        key.timeExpires()
          .map(OffsetDateTime::toString)
          .orElse("Never")
      );

    for (final var user : key.userIDs()) {
      builder.addRow()
        .addCell("User ID")
        .addCell(user);
    }

    this.renderTable(builder.build());

    final var out = this.terminal.writer();
    out.println(key.encodedForm());
    out.flush();
  }

  @Override
  public void formatPublicKeySummaries(
    final NPPage<NPPublicKeySummary> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(4))
        .declareColumn("Fingerprint", atLeastContentOrHeader())
        .declareColumn("Time Created", atLeastContentOrHeader())
        .declareColumn("Time Expires", atLeastContentOrHeader())
        .declareColumn("User ID", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.fingerprint().toString())
        .addCell(item.timeCreated().withNano(0).toString())
        .addCell(
          item.timeExpires()
            .map(x -> x.withNano(0))
            .map(OffsetDateTime::toString)
            .orElse("Never")
        )
        .addCell(
          StringUtils.abbreviate(
            String.join(", ", item.userID()), 30
          )
        );
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatFingerprints(
    final Set<NPFingerprint> keys)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Attribute", atLeastContentOrHeader())
        .declareColumn("Value", atLeastContentOrHeader());

    for (final var key : keys) {
      builder.addRow()
        .addCell("Fingerprint")
        .addCell(key.value());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatSCMProviders(
    final Set<NPSCMProviderDescription> providers)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(3))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("URI", atLeastContentOrHeader())
        .declareColumn("Description", atLeastContentOrHeader());

    for (final var provider : providers) {
      builder.addRow()
        .addCell(provider.name().value())
        .addCell(provider.uri().toString())
        .addCell(provider.description());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatUserID(final UUID id)
  {
    final var out = this.terminal.writer();
    out.println(id.toString());
  }

  @Override
  public void formatUsers(
    final NPPage<NPUser> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(3))
        .declareColumn("ID", atLeastContentOrHeader())
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Roles", any());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.userId().toString())
        .addCell(item.name().value())
        .addCell(
          item.subject()
            .roles()
            .stream()
            .map(MRoleName::value)
            .sorted()
            .toList()
            .toString()
        );
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatAgent(
    final NPAgentDescription agent)
    throws Exception
  {
    final var out = this.terminal.writer();

    {
      final var builder =
        Tabla.builder()
          .setWidthConstraint(this.softTableWidth(2))
          .declareColumn("Attribute", atLeastContentOrHeader())
          .declareColumn("Value", atLeastContentOrHeader());

      builder.addRow()
        .addCell("ID")
        .addCell(agent.id().toString());
      builder.addRow()
        .addCell("Name")
        .addCell(agent.name());
      builder.addRow()
        .addCell("Public Key")
        .addCell("%s:%s".formatted(
          agent.publicKey().algorithm(),
          agent.publicKey().asText()
        ));

      this.renderTable(builder.build());
    }

    if (agent.labels().size() > 0) {
      out.println("Labels");

      final var builder =
        Tabla.builder()
          .setWidthConstraint(this.softTableWidth(1))
          .declareColumn("Name", any());

      final var values =
        agent.labels()
          .values()
          .stream()
          .sorted()
          .toList();

      for (final var name : values) {
        builder.addRow()
          .addCell(name.name().toString());
      }

      this.renderTable(builder.build());
    }

    if (agent.systemProperties().size() > 0) {
      out.println("System Properties");

      final var builder =
        Tabla.builder()
          .setWidthConstraint(this.softTableWidth(2))
          .declareColumn("Name", atLeastContentOrHeader())
          .declareColumn("Value", atLeastContentOrHeader());

      final var sortedEntries =
        agent.systemProperties()
          .entrySet()
          .stream()
          .sorted(Map.Entry.comparingByKey())
          .toList();

      for (final var entry : sortedEntries) {
        builder.addRow()
          .addCell(entry.getKey())
          .addCell(entry.getValue());
      }

      this.renderTable(builder.build());
    }

    if (agent.environmentVariables().size() > 0) {
      out.println("Environment Variables");

      final var builder =
        Tabla.builder()
          .setWidthConstraint(this.softTableWidth(2))
          .declareColumn("Name", atLeastContentOrHeader())
          .declareColumn("Value", atLeastContentOrHeader());

      final var sortedEntries =
        agent.systemProperties()
          .entrySet()
          .stream()
          .sorted(Map.Entry.comparingByKey())
          .toList();

      for (final var entry : sortedEntries) {
        builder.addRow()
          .addCell(entry.getKey())
          .addCell(entry.getValue());
      }

      this.renderTable(builder.build());
    }
  }

  @Override
  public void formatAgentSummaries(
    final NPPage<NPAgentSummary> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("ID", atLeastContentOrHeader())
        .declareColumn("Name", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.id().toString())
        .addCell(item.name());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatAgentLabel(
    final NPAgentLabel label)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Description", atLeastContentOrHeader());

    builder.addRow()
      .addCell(label.name().toString())
      .addCell(label.description());

    this.renderTable(builder.build());
  }

  @Override
  public void formatAgentLabels(
    final NPPage<NPAgentLabel> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Description", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.name().toString())
        .addCell(item.description());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatToolExecutionDescriptionSummaries(
    final NPPage<NPToolExecutionDescriptionSummary> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(4))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Version", atLeastContentOrHeader())
        .declareColumn("Tool", atLeastContentOrHeader())
        .declareColumn("Description", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.identifier().name().toString())
        .addCell(Long.toUnsignedString(item.identifier().version()))
        .addCell(item.tool().toString())
        .addCell(item.description());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatToolExecutionDescription(
    final NPToolExecutionDescription data)
  {
    final var out = this.terminal.writer();
    out.println(data.text());
  }

  @Override
  public void formatPlan(
    final NPPlanDescriptionUnparsed plan)
  {
    final var out = this.terminal.writer();
    out.println(plan.text());
  }

  @Override
  public void formatPlanSummaries(
    final NPPage<NPPlanSummary> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(3))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Version", atLeastContentOrHeader())
        .declareColumn("Description", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.identifier().name().toString())
        .addCell(Long.toUnsignedString(item.identifier().version()))
        .addCell(item.description());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatAgentIDs(
    final Set<NPAgentID> agents)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(1))
        .declareColumn("ID", atLeastContentOrHeader());

    for (final var item : agents) {
      builder.addRow()
        .addCell(item.toString());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatWorkItems(
    final Set<NPWorkItem> workItems)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(4))
        .declareColumn("Assignment Execution", atLeastContentOrHeader())
        .declareColumn("Element", atLeastContentOrHeader())
        .declareColumn("Agent", atLeastContentOrHeader())
        .declareColumn("Status", atLeastContentOrHeader());

    for (final var item : workItems) {
      builder.addRow()
        .addCell(item.identifier().assignmentExecutionId().toString())
        .addCell(item.identifier().planElementName().toString())
        .addCell(item.selectedAgent().map(NPAgentID::toString).orElse(null))
        .addCell(item.status().toString());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatAssignment(
    final NPAssignment assignment)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Attribute", atLeastContentOrHeader())
        .declareColumn("Value", atLeastContentOrHeader());

    builder.addRow()
      .addCell("Name")
      .addCell(assignment.name().toString());
    builder.addRow()
      .addCell("Plan")
      .addCell(
        "%s %s".formatted(
          assignment.plan().name(),
          Long.toUnsignedString(assignment.plan().version())
        )
      );
    builder.addRow()
      .addCell("Repository")
      .addCell(assignment.repositoryId().toString());
    builder.addRow()
      .addCell("Schedule")
      .addCell(formatSchedule(assignment.schedule()));

    this.renderTable(builder.build());
  }

  @Override
  public void formatAssignments(
    final NPPage<NPAssignment> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(4))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Plan", atLeastContentOrHeader())
        .declareColumn("Repository", atLeastContentOrHeader())
        .declareColumn("Schedule", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.name().toString())
        .addCell("%s %s".formatted(
          item.plan().name(),
          Long.toUnsignedString(item.plan().version())
        ))
        .addCell(item.repositoryId().toString())
        .addCell(formatSchedule(item.schedule()));
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatAgentNames(
    final List<NPAgentLocalName> names)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(1))
        .declareColumn("Name", atLeastContentOrHeader());

    for (final var item : names) {
      builder.addRow().addCell(item.toString());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatServerSummaries(
    final List<NPAgentServerSummary> summaries)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("ID", atLeastContentOrHeader())
        .declareColumn("Hostname", atLeastContentOrHeader());

    for (final var item : summaries) {
      builder.addRow()
        .addCell(item.id().toString())
        .addCell(item.hostname());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatAgentResult(
    final NPAgentLocalName name,
    final NPAgentKeyPublicType publicKey,
    final Optional<NPAgentServerID> server,
    final Optional<NPAWorkExecutorConfiguration> workExec)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Attribute", atLeastContentOrHeader())
        .declareColumn("Value", atLeastContentOrHeader());

    builder.addRow()
      .addCell("Name")
      .addCell(name.toString());

    builder.addRow()
      .addCell("Public Key Algorithm")
      .addCell(publicKey.algorithm());

    builder.addRow()
      .addCell("Public Key")
      .addCell(publicKey.asText());

    if (server.isPresent()) {
      builder.addRow()
        .addCell("Server")
        .addCell(server.get().toString());
    }

    this.renderTable(builder.build());

    if (workExec.isPresent()) {
      this.formatWorkExecutor(workExec.get());
    }
  }

  @Override
  public void formatWorkExecutor(
    final NPAWorkExecutorConfiguration workExec)
    throws Exception
  {
    final var out = this.terminal.writer();
    out.println("Work Executor");

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Attribute", atLeastContentOrHeader())
        .declareColumn("Value", atLeastContentOrHeader());

    builder.addRow()
      .addCell("Work Directory")
      .addCell(workExec.workDirectory().toString());

    builder.addRow()
      .addCell("Temporary Directory")
      .addCell(workExec.temporaryDirectory().toString());

    if (workExec.workExecDistributionDirectory().isPresent()) {
      builder.addRow()
        .addCell("Distribution Directory")
        .addCell(workExec.workExecDistributionDirectory().get().toString());
    }

    if (workExec.containerImage().isPresent()) {
      final var image = workExec.containerImage().get();
      builder.addRow()
        .addCell("OCI Registry")
        .addCell(image.registry());
      builder.addRow()
        .addCell("OCI Image Name")
        .addCell(image.name());
      builder.addRow()
        .addCell("OCI Image Tag")
        .addCell(image.tag());
      if (image.hash().isPresent()) {
        builder.addRow()
          .addCell("OCI Image Hash")
          .addCell(image.hash().get());
      }
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatAgentServer(
    final NPAgentServerDescription server)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Attribute", atLeastContentOrHeader())
        .declareColumn("Value", atLeastContentOrHeader());

    builder.addRow()
      .addCell("ID")
      .addCell(server.id().toString());

    builder.addRow()
      .addCell("Hostname")
      .addCell(server.hostname());

    builder.addRow()
      .addCell("Port")
      .addCell(Integer.toUnsignedString(server.port()));

    builder.addRow()
      .addCell("Message Size Limit")
      .addCell(Integer.toUnsignedString(server.messageSizeLimit()));

    this.renderTable(builder.build());

    final var out = this.terminal.writer();
    out.println("TLS");

    this.formatTLS(server.tls());
  }

  @Override
  public void formatTLS(
    final NPTLSConfigurationType tls)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Attribute", atLeastContentOrHeader())
        .declareColumn("Value", atLeastContentOrHeader());

    switch (tls) {
      case final NPTLSDisabled ignored -> {
        builder.addRow()
          .addCell("Type")
          .addCell("Disabled");
      }

      case final NPTLSEnabledExplicit e -> {
        builder.addRow()
          .addCell("Type")
          .addCell("Enabled (Explicit)");
        builder.addRow()
          .addCell("Key Store Type")
          .addCell(e.keyStore().storeType());
        builder.addRow()
          .addCell("Key Store Provider")
          .addCell(e.keyStore().storeProvider());
        builder.addRow()
          .addCell("Key Store Path")
          .addCell(e.keyStore().storePath().toString());
        builder.addRow()
          .addCell("Key Store Password")
          .addCell(e.keyStore().storePassword());

        builder.addRow()
          .addCell("Trust Store Type")
          .addCell(e.trustStore().storeType());
        builder.addRow()
          .addCell("Trust Store Provider")
          .addCell(e.trustStore().storeProvider());
        builder.addRow()
          .addCell("Trust Store Path")
          .addCell(e.trustStore().storePath().toString());
        builder.addRow()
          .addCell("Trust Store Password")
          .addCell(e.trustStore().storePassword());
      }

      case final NPTLSEnabledClientAnonymous ignored -> {
        builder.addRow()
          .addCell("Type")
          .addCell("Enabled (Anonymous)");
      }
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatAgentLoginChallenges(
    final NPPage<NPAgentLoginChallengeRecord> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(4))
        .declareColumn("Time", atLeastContentOrHeader())
        .declareColumn("ID", atLeastContentOrHeader())
        .declareColumn("Source", atLeastContentOrHeader())
        .declareColumn("Key", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.timeCreated().toString())
        .addCell(item.id().toString())
        .addCell(item.sourceAddress())
        .addCell(item.key().asText());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatBookmarks(
    final List<NPPreferenceServerBookmark> bookmarks)
    throws Exception
  {
    if (bookmarks.isEmpty()) {
      return;
    }

    final var tableBuilder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(5))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Host", atLeastContentOrHeader())
        .declareColumn("Port", atLeastContentOrHeader())
        .declareColumn("TLS", atLeastContentOrHeader())
        .declareColumn("User", atLeastContentOrHeader());

    for (final var bookmark : bookmarks) {
      tableBuilder.addRow()
        .addCell(bookmark.name())
        .addCell(bookmark.host())
        .addCell(Integer.toString(bookmark.port()))
        .addCell(bookmark.tlsConfiguration().kind().name())
        .addCell(userOf(bookmark.credentials()));
    }

    this.renderTable(tableBuilder.build());
  }

  @Override
  public void formatAgentStatuses(
    final Map<NPAgentLocalName, NPAgentStatus> status)
    throws Exception
  {
    if (status.isEmpty()) {
      return;
    }

    final var tableBuilder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(3))
        .declareColumn("Agent", atLeastContentOrHeader())
        .declareColumn("Health", TColumnWidthConstraint.exactWidth(12))
        .declareColumn("Status", atLeastContentOrHeader());

    final var sorted = new TreeMap<>(status);
    for (final var entry : sorted.entrySet()) {
      final var name = entry.getKey();
      final var statusValue = entry.getValue();
      tableBuilder.addRow()
        .addCell(name.toString())
        .addCell(statusValue.health().name())
        .addCell(statusValue.description());
    }

    this.renderTable(tableBuilder.build());
  }

  @Override
  public void formatWorkExecutorSummaries(
    final List<NPAWorkExecutorSummary> summaries)
    throws Exception
  {
    if (summaries.isEmpty()) {
      return;
    }

    final var tableBuilder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Description", atLeastContentOrHeader());

    for (final var summary : summaries) {
      tableBuilder.addRow()
        .addCell(summary.name().toString())
        .addCell(summary.description());
    }

    this.renderTable(tableBuilder.build());
  }

  @Override
  public void formatWorkExecutorSummary(
    final NPAWorkExecutorSummary summary)
    throws Exception
  {
    {
      final var builder =
        Tabla.builder()
          .setWidthConstraint(this.softTableWidth(2))
          .declareColumn("Attribute", atLeastContentOrHeader())
          .declareColumn("Value", atLeastContentOrHeader());

      builder.addRow()
        .addCell("Name")
        .addCell(summary.name().toString());

      builder.addRow()
        .addCell("Description")
        .addCell(summary.description());

      this.renderTable(builder.build());
    }

    if (summary.properties().isEmpty()) {
      return;
    }

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(1))
        .declareColumn("Property", atLeastContentOrHeader());

    for (final var property : summary.properties()) {
      builder.addRow().addCell(property.toString());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatTools(
    final NPPage<NPToolSummary> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Description", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.name().toString())
        .addCell(item.description());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatTool(
    final NPToolDescription toolDescription)
    throws Exception
  {
    {
      final var builder =
        Tabla.builder()
          .setWidthConstraint(this.softTableWidth(2))
          .declareColumn("Attribute", atLeastContentOrHeader())
          .declareColumn("Value", atLeastContentOrHeader());

      builder.addRow()
        .addCell("Name")
        .addCell(toolDescription.name().toString());

      builder.addRow()
        .addCell("Description")
        .addCell(toolDescription.description());

      builder.addRow()
        .addCell("Versions Supported")
        .addCell(toolDescription.versions().toString());

      this.renderTable(builder.build());
    }

    if (toolDescription.defaultExecutions().isEmpty()) {
      return;
    }

    final var out = this.terminal.writer();
    out.println("Tool Executions");

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Arguments", atLeastContentOrHeader());

    for (final var entry : toolDescription.defaultExecutions().entrySet()) {
      builder.addRow()
        .addCell(entry.getKey().toString())
        .addCell(entry.getValue().toString());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatPlanFormats(
    final Set<NPPlanFormatDescription> formats)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Name", atLeastContentOrHeader())
        .declareColumn("Description", atLeastContentOrHeader());

    final var sorted =
      formats.stream()
        .sorted(Comparator.comparing(NPPlanFormatDescription::name))
        .toList();

    for (final var format : sorted) {
      builder.addRow()
        .addCell(format.name().toString())
        .addCell(format.description());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatAssignmentExecutions(
    final NPPage<NPAssignmentExecutionStateType> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(5))
        .declareColumn("ID", atLeastContentOrHeader())
        .declareColumn("Created", atLeastContentOrHeader())
        .declareColumn("Status", atLeastContentOrHeader())
        .declareColumn("Assignment", atLeastContentOrHeader())
        .declareColumn("Commit", atLeastContentOrHeader());

    for (final var format : page.items()) {
      builder.addRow()
        .addCell(format.id().toString())
        .addCell(format.timeCreated().toString())
        .addCell(format.stateName())
        .addCell(format.request().assignment().toString())
        .addCell(format.request().commit().value());
    }

    this.renderTable(builder.build());
  }

  private static String userOf(
    final NPPreferenceServerCredentialsType credentials)
  {
    return switch (credentials) {
      case final NPPreferenceServerUsernamePassword u -> u.username();
    };
  }

  private static void formatPage(
    final NPPage<?> page,
    final PrintWriter out)
  {
    out.printf(
      " Page %s of %s, offset %s%n",
      Integer.toUnsignedString(page.pageIndex()),
      Integer.toUnsignedString(page.pageCount()),
      Long.toUnsignedString(page.pageFirstOffset())
    );
  }

  private void renderTable(
    final TTableType table)
  {
    final var lines =
      this.tableRenderer.renderLines(table);

    final var writer = this.terminal.writer();
    for (final var line : lines) {
      writer.println(line);
    }
  }
}
