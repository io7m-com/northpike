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

import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.model.NPAuditEvent;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositorySummary;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionDescriptionSummary;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.model.agents.NPAgentLabel;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.agents.NPAgentServerSummary;
import com.io7m.northpike.model.agents.NPAgentSummary;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleHourlyHashed;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleType;
import com.io7m.northpike.model.plans.NPPlanDescriptionUnparsed;
import com.io7m.northpike.model.plans.NPPlanSummary;
import com.io7m.northpike.model.tls.NPTLSConfigurationType;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.model.tls.NPTLSEnabled;
import org.jline.terminal.Terminal;

import java.io.PrintWriter;
import java.time.OffsetDateTime;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.stream.Collectors;

/**
 * A raw formatter.
 */

public final class NPFormatterRaw implements NPFormatterType
{
  private final Terminal terminal;

  /**
   * A raw formatter.
   *
   * @param inTerminal The terminal
   */

  public NPFormatterRaw(
    final Terminal inTerminal)
  {
    this.terminal =
      Objects.requireNonNull(inTerminal, "terminal");
  }

  @Override
  public String toString()
  {
    return "[%s]".formatted(this.getClass().getSimpleName());
  }

  @Override
  public void formatAudits(
    final NPPage<NPAuditEvent> page)
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    out.println("# ID | Time | Owner | Type | Message");

    for (final var audit : page.items()) {
      out.printf(
        "%12s | %-24s | %-36s | %-24s | %s%n",
        Long.toUnsignedString(audit.id()),
        audit.time(),
        audit.owner(),
        audit.type(),
        audit.data()
      );
    }
    out.flush();
  }

  @Override
  public void formatRepository(
    final NPRepositoryDescription repository)
  {
    final var out = this.terminal.writer();
    out.print("ID: ");
    out.println(repository.id());
    out.print("SCM Provider: ");
    out.println(repository.provider());
    out.print("URI: ");
    out.println(repository.url());
    out.print("Credentials: ");
    out.println(repository.credentials());
    out.print("Signing Policy: ");
    out.println(repository.signingPolicy());
    out.flush();
  }

  @Override
  public void formatRepositorySummaries(
    final NPPage<NPRepositorySummary> page)
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    out.println("# ID | Provider | URI");

    for (final var item : page.items()) {
      out.printf(
        "%-24s | %-36s | %s%n",
        item.id(),
        item.provider(),
        item.url()
      );
    }
    out.flush();
  }

  @Override
  public void formatPublicKey(
    final NPPublicKey key)
  {
    final var out = this.terminal.writer();
    out.println(key.encodedForm());
  }

  @Override
  public void formatPublicKeySummaries(
    final NPPage<NPPublicKey> page)
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    out.println("# Fingerprint | Time Created | Time Expires | User IDs");

    for (final var item : page.items()) {
      out.printf(
        "%-40s | %s | %s | %s%n",
        item.fingerprint(),
        item.timeCreated(),
        item.timeExpires()
          .map(OffsetDateTime::toString)
          .orElse("Never"),
        item.userIDs()
      );
    }
    out.flush();
  }

  @Override
  public void formatFingerprints(
    final Set<NPFingerprint> keys)
  {
    final var out = this.terminal.writer();
    for (final var key : keys) {
      out.println(key.value());
    }
    out.flush();
  }

  @Override
  public void formatSCMProviders(
    final Set<NPSCMProviderDescription> providers)
  {
    final var out = this.terminal.writer();
    out.println("# Name | URI | Description");

    for (final var provider : providers) {
      out.printf(
        "%s | %s | %s%n",
        provider.name().value(),
        provider.uri().toString(),
        provider.description()
      );
    }
    out.flush();
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
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    out.println("# ID | Name | Roles");

    for (final var item : page.items()) {
      out.printf(
        "%-40s | %s | %s%n",
        item.userId(),
        item.name().value(),
        item.subject()
          .roles()
          .stream()
          .map(x -> x.value().value())
          .collect(Collectors.toUnmodifiableSet())
      );
    }
    out.flush();
  }

  @Override
  public void formatAgent(
    final NPAgentDescription agent)
  {
    final var out = this.terminal.writer();
    out.print("ID: ");
    out.println(agent.id());
    out.print("Name: ");
    out.println(agent.name());
    out.print("Access Key: ");
    out.print(agent.publicKey().algorithm());
    out.print(":");
    out.println(agent.publicKey().asText());

    if (agent.labels().size() > 0) {
      for (final var name : agent.labels().values()) {
        out.print("Label: ");
        out.println(name.name().toString());
      }
    }

    if (agent.systemProperties().size() > 0) {
      for (final var entry : agent.systemProperties().entrySet()) {
        out.print("SystemProperty: ");
        out.println(entry.getKey() + " " + entry.getValue());
      }
    }

    if (agent.environmentVariables().size() > 0) {
      for (final var entry : agent.environmentVariables().entrySet()) {
        out.print("Environment: ");
        out.println(entry.getKey() + " " + entry.getValue());
      }
    }

    out.flush();
  }

  @Override
  public void formatAgentSummaries(
    final NPPage<NPAgentSummary> page)
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    out.println("# ID | Name");

    for (final var item : page.items()) {
      out.printf(
        "%-40s | %s%n",
        item.id(),
        item.name()
      );
    }
    out.flush();
  }

  @Override
  public void formatAgentLabel(
    final NPAgentLabel label)
  {
    final var out = this.terminal.writer();
    out.print(label.name());
    out.print(": ");
    out.print(label.description());
    out.println();
    out.flush();
  }

  @Override
  public void formatAgentLabels(
    final NPPage<NPAgentLabel> page)
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    out.println("# Name | Description");

    for (final var item : page.items()) {
      out.printf(
        "%s | %s%n",
        item.name(),
        item.description()
      );
    }
    out.flush();
  }

  @Override
  public void formatToolExecutionDescriptionSummaries(
    final NPPage<NPToolExecutionDescriptionSummary> page)
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    out.println("# Name | Version | Tool | Description");

    for (final var item : page.items()) {
      out.printf(
        "%s | %s | %s | %s%n",
        item.identifier().name(),
        Long.toUnsignedString(item.identifier().version()),
        item.tool(),
        item.description()
      );
    }
    out.flush();
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
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    out.println("# Name | Version | Description");

    for (final var item : page.items()) {
      out.printf(
        "%s | %s | %s%n",
        item.identifier().name(),
        Long.toUnsignedString(item.identifier().version()),
        item.description()
      );
    }
    out.flush();
  }

  @Override
  public void formatAgentIDs(
    final Set<NPAgentID> agents)
  {
    final var out = this.terminal.writer();
    out.println("# ID");

    for (final var item : agents) {
      out.printf("%s%n", item);
    }
    out.flush();
  }

  @Override
  public void formatWorkItems(
    final Set<NPWorkItem> workItems)
  {
    final var out = this.terminal.writer();
    out.println("# Assignment Execution | Task | Agent | Status");

    for (final var item : workItems) {
      out.printf(
        "%s | %s | %s | %s%n",
        item.identifier().assignmentExecutionId(),
        item.identifier().planElementName(),
        item.selectedAgent().orElse(null),
        item.status()
      );
    }
    out.flush();
  }

  @Override
  public void formatAssignment(
    final NPAssignment assignment)
  {
    final var out = this.terminal.writer();
    out.print("Name: ");
    out.println(assignment.name());

    out.print("Plan: ");
    out.println("%s %s".formatted(
      assignment.plan().name(),
      Long.toUnsignedString(assignment.plan().version())
    ));

    out.print("Repository: ");
    out.println(assignment.repositoryId());

    out.println("Schedule: " + formatSchedule(assignment.schedule()));
    out.flush();
  }

  @Override
  public void formatAssignments(
    final NPPage<NPAssignment> page)
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    out.println("# Name | Plan | Repository | Schedule");

    for (final var item : page.items()) {
      out.printf(
        "%s | %s | %s | %s%n",
        item.name(),
        "%s %s".formatted(
          item.plan().name(),
          Long.toUnsignedString(item.plan().version())
        ),
        item.repositoryId(),
        formatSchedule(item.schedule())
      );
    }
    out.flush();
  }

  @Override
  public void formatAgentNames(
    final List<NPAgentLocalName> names)
  {
    final var out = this.terminal.writer();
    for (final var item : names) {
      out.println(item.toString());
    }
    out.flush();
  }

  @Override
  public void formatServerSummaries(
    final List<NPAgentServerSummary> summaries)
  {
    final var out = this.terminal.writer();
    for (final var item : summaries) {
      out.printf("%s %s%n", item.id(), item.hostname());
    }
    out.flush();
  }

  @Override
  public void formatAgentResult(
    final NPAgentLocalName name,
    final NPAgentKeyPublicType publicKey,
    final Optional<NPAgentServerID> server,
    final Optional<NPAWorkExecutorConfiguration> workExec)
  {
    final var out = this.terminal.writer();
    out.print("Name: ");
    out.println(name);

    out.print("Public Key: ");
    out.println(publicKey.asText());

    if (server.isPresent()) {
      out.print("Server: ");
      out.println(server.get());
    }

    if (workExec.isPresent()) {
      final var we = workExec.get();
      this.formatWorkExecutor(we);
    }
  }

  @Override
  public void formatWorkExecutor(
    final NPAWorkExecutorConfiguration workExec)
  {
    final var out = this.terminal.writer();
    out.print("WorkExec Type: ");
    out.println(workExec.type());

    out.print("WorkExec Temporary Directory: ");
    out.println(workExec.temporaryDirectory());

    out.print("WorkExec Work Directory: ");
    out.println(workExec.workDirectory());

    if (workExec.workExecDistributionDirectory().isPresent()) {
      out.print("WorkExec Distribution Directory: ");
      out.println(workExec.workExecDistributionDirectory().get());
    }

    if (workExec.containerImage().isPresent()) {
      final var image = workExec.containerImage().get();
      out.print("OCI Registry: ");
      out.println(image.registry());
      out.print("OCI Image Name: ");
      out.println(image.name());
      out.print("OCI Image Tag: ");
      out.println(image.tag());
      if (image.hash().isPresent()) {
        out.print("OCI Image Hash: ");
        out.println(image.hash().get());
      }
    }
  }

  @Override
  public void formatAgentServer(
    final NPAgentServerDescription server)
    throws Exception
  {
    final var out = this.terminal.writer();
    out.print("ID: ");
    out.println(server.id());

    out.print("Hostname: ");
    out.println(server.hostname());

    out.print("Port: ");
    out.println(server.port());

    this.formatTLS(server.tls());

    out.print("Message Size Limit: ");
    out.println(server.messageSizeLimit());

    out.flush();
  }

  @Override
  public void formatTLS(
    final NPTLSConfigurationType tls)
  {
    final var out = this.terminal.writer();

    switch (tls) {
      case final NPTLSDisabled d -> {
        out.printf("TLS: %s%n", d);
      }
      case final NPTLSEnabled e -> {
        out.print("TLS Key Store Type: ");
        out.println(e.keyStore().storeType());
        out.print("TLS Key Store Provider: ");
        out.println(e.keyStore().storeProvider());
        out.print("TLS Key Store Path: ");
        out.println(e.keyStore().storePath());
        out.print("TLS Key Store Password: ");
        out.println(e.keyStore().storePassword());

        out.print("TLS Trust Store Type: ");
        out.println(e.trustStore().storeType());
        out.print("TLS Trust Store Provider: ");
        out.println(e.trustStore().storeProvider());
        out.print("TLS Trust Store Path: ");
        out.println(e.trustStore().storePath());
        out.print("TLS Trust Store Password: ");
        out.println(e.trustStore().storePassword());
      }
    }

    out.flush();
  }

  static String formatSchedule(
    final NPAssignmentScheduleType schedule)
  {
    return switch (schedule) {
      case final NPAssignmentScheduleNone none -> "None";
      case final NPAssignmentScheduleHourlyHashed hashed ->
        "HourlyHashed (Commit age cutoff: %s)"
          .formatted(hashed.commitAgeCutoff());
    };
  }

  private static void formatPage(
    final NPPage<?> page,
    final PrintWriter out)
  {
    out.printf(
      "# Page %s of %s, offset %s%n",
      Integer.toUnsignedString(page.pageIndex()),
      Integer.toUnsignedString(page.pageCount()),
      Long.toUnsignedString(page.pageFirstOffset())
    );
  }
}
