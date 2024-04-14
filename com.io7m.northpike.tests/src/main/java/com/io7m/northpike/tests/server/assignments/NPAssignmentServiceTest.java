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


package com.io7m.northpike.tests.server.assignments;

import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.ervilla.test_extension.ErvillaCloseAfterSuite;
import com.io7m.ervilla.test_extension.ErvillaConfiguration;
import com.io7m.ervilla.test_extension.ErvillaExtension;
import com.io7m.northpike.clock.NPClock;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentExecutionGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentExecutionLogListType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPHash;
import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreationFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateSucceeded;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.model.plans.NPPlanType;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanParsers;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.archives.NPArchiveServiceType;
import com.io7m.northpike.server.internal.assignments.NPAssignmentService;
import com.io7m.northpike.server.internal.assignments.NPAssignmentServiceType;
import com.io7m.northpike.server.internal.metrics.NPMetricsService;
import com.io7m.northpike.server.internal.metrics.NPMetricsServiceType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventService;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.tests.NPEventInterceptingService;
import com.io7m.northpike.tests.containers.NPDatabaseFixture;
import com.io7m.northpike.tests.containers.NPFixtures;
import com.io7m.northpike.toolexec.api.NPTEvaluationService;
import com.io7m.northpike.toolexec.api.NPTEvaluationServiceType;
import com.io7m.repetoir.core.RPServiceDirectory;
import com.io7m.repetoir.core.RPServiceDirectoryWritableType;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mockito;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.URI;
import java.time.Clock;
import java.time.OffsetDateTime;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorIo;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.mockito.ArgumentMatchers.any;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPAssignmentServiceTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAssignmentService.class);

  private static final NPStrings STRINGS = NPStrings.create(Locale.ROOT);
  private static NPAssignmentFixture ASSIGNMENT_FIXTURE;
  private static NPDatabaseFixture DATABASE_FIXTURE;
  private RPServiceDirectoryWritableType services;
  private NPEventInterceptingService events;
  private NPAgentServiceType agents;
  private NPRepositoryServiceType repositories;
  private NPArchiveServiceType archives;
  private NPDatabaseType database;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers)
    throws Exception
  {
    DATABASE_FIXTURE =
      NPFixtures.database(NPFixtures.pod(containers));
    ASSIGNMENT_FIXTURE =
      NPFixtures.assignment(NPFixtures.pod(containers));
  }

  @BeforeEach
  public void setup(
    final CloseableResourcesType closeables)
    throws Exception
  {
    ASSIGNMENT_FIXTURE.reset(closeables);

    this.services = new RPServiceDirectory();
    this.services.register(
      NPStrings.class, STRINGS);
    this.database =
      DATABASE_FIXTURE.createDatabase();
    this.services.register(
      NPDatabaseType.class, this.database);
    this.services.register(
      NPTelemetryServiceType.class, NPTelemetryNoOp.noop());
    this.services.register(
      NPMetricsServiceType.class, new NPMetricsService(NPTelemetryNoOp.noop()));
    this.services.register(
      NPClockServiceType.class, new NPClock(Clock.systemUTC()));
    this.services.register(
      NPPlanParserFactoryType.class, new NPPlanParsers());

    this.archives =
      Mockito.mock(NPArchiveServiceType.class);
    this.services.register(
      NPArchiveServiceType.class, this.archives);

    this.repositories =
      Mockito.mock(NPRepositoryServiceType.class);
    this.services.register(
      NPRepositoryServiceType.class, this.repositories);

    this.agents =
      Mockito.mock(NPAgentServiceType.class);
    this.services.register(
      NPAgentServiceType.class, this.agents);

    this.events =
      new NPEventInterceptingService(
        NPEventService.create(NPTelemetryNoOp.noop())
      );
    this.services.register(NPEventServiceType.class, this.events);
    this.services.register(
      NPTEvaluationServiceType.class,
      NPTEvaluationService.createFromServiceLoader(NPStrings.create(Locale.ROOT))
    );
  }

  @AfterEach
  public void tearDown()
    throws IOException
  {
    this.services.close();
  }

  private static NPPlanType createPlanEmptyTask()
    throws NPPlanException
  {
    return NPPlans.builder(STRINGS, "plans.empty", 1L)
      .build();
  }

  /**
   * A nonexistent commit fails immediately.
   *
   * @throws Exception On errors
   */

  @Test
  public void testNonexistentCommit()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS,
        createPlanEmptyTask()
      );

    final var assignmentService =
      NPAssignmentService.create(this.services);

    final var inProgress =
      assignmentService.requestExecution(
        new NPAssignmentExecutionRequest(
          assignment.name(),
          new NPCommitUnqualifiedID("abcd")
        )
      );

    inProgress.future().get(10L, TimeUnit.SECONDS);

    final var state =
      this.retrieveState(inProgress);

    assertInstanceOf(NPAssignmentExecutionStateCreationFailed.class, state);

    this.logEvents();
    this.logOutput(inProgress.executionId());
  }

  /**
   * A nonexistent assignment fails immediately.
   *
   * @throws Exception On errors
   */

  @Test
  public void testNonexistentAssignment()
    throws Exception
  {
    final var assignmentService =
      NPAssignmentService.create(this.services);

    final var inProgress =
      assignmentService.requestExecution(
        new NPAssignmentExecutionRequest(
          NPAssignmentName.of("nonexistent"),
          new NPCommitUnqualifiedID("abcd")
        )
      );

    inProgress.future().get(10L, TimeUnit.SECONDS);

    final var state =
      this.retrieveState(inProgress);

    assertInstanceOf(NPAssignmentExecutionStateCreationFailed.class, state);

    this.logEvents();
    this.logOutput(inProgress.executionId());
  }

  private void logEvents()
  {
    this.events.eventQueue()
      .forEach(e -> LOG.debug("EVENT {}", e));
  }

  /**
   * An empty plan succeeds immediately.
   *
   * @throws Exception On errors
   */

  @Test
  public void testEmptyPlanSucceedImmediately()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS,
        createPlanEmptyTask()
      );

    final var assignmentService =
      NPAssignmentService.create(this.services);

    final var archive =
      new NPArchive(
        NPToken.generate(),
        ASSIGNMENT_FIXTURE.commitUnsigned(),
        new NPHash(
          "SHA-256",
          "01ba4719c80b6fe911b091a7c05124b64eeece964e09c058ef8f9805daca546b"),
        OffsetDateTime.now()
      );

    Mockito.when(this.archives.linksForArchive(archive))
      .thenReturn(new NPArchiveLinks(
        URI.create("http://example.com/sources"),
        URI.create("http://example.com/checksum")
      ));

    Mockito.when(this.repositories.commitGet(any()))
      .thenReturn(
        new NPCommit(
          ASSIGNMENT_FIXTURE.commitUnsigned(),
          OffsetDateTime.now(),
          OffsetDateTime.now(),
          new NPCommitAuthor("Author", "someone@example.com"),
          "Subject",
          "Body",
          Set.of(),
          Set.of()
        )
      );

    Mockito.when(this.repositories.repositorySigningPolicyFor(any()))
      .thenReturn(ALLOW_UNSIGNED_COMMITS);

    Mockito.when(this.repositories.repositoryUpdate(any()))
      .thenReturn(CompletableFuture.completedFuture(null));

    Mockito.when(this.repositories.commitCreateArchiveFor(any()))
      .thenReturn(archive);

    final var inProgress =
      assignmentService.requestExecution(
        new NPAssignmentExecutionRequest(
          assignment.name(),
          ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
        )
      );

    inProgress.future().get(10L, TimeUnit.SECONDS);

    final var state =
      this.retrieveState(inProgress);

    assertInstanceOf(NPAssignmentExecutionStateSucceeded.class, state);

    this.logEvents();
    this.logOutput(inProgress.executionId());
  }

  /**
   * An empty plan with a crashing archive service fails immediately.
   *
   * @throws Exception On errors
   */

  @Test
  public void testArchiveServiceCrashes()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS, createPlanEmptyTask());

    final var assignmentService =
      NPAssignmentService.create(this.services);

    Mockito.when(this.repositories.commitCreateArchiveFor(any()))
      .thenThrow(new NPException("Ouch!", errorIo(), Map.of(), Optional.empty()));

    final var inProgress =
      assignmentService.requestExecution(
        new NPAssignmentExecutionRequest(
          assignment.name(),
          ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
        )
      );

    inProgress.future().get(10L, TimeUnit.SECONDS);

    final var state =
      this.retrieveState(inProgress);

    assertInstanceOf(NPAssignmentExecutionStateCreationFailed.class, state);

    this.logEvents();
    this.logOutput(inProgress.executionId());
  }

  private void logOutput(final NPAssignmentExecutionID execution)
    throws NPDatabaseException
  {
    try (var connection = this.database.openConnection(NPDatabaseRole.NORTHPIKE)) {
      try (var transaction = connection.openTransaction()) {
        final var paged =
          transaction.queries(AssignmentExecutionLogListType.class)
            .execute(
              new AssignmentExecutionLogListType.Parameters(
                execution,
                true,
                1000L
              )
            );

        var page = paged.pageCurrent(transaction);
        for (int index = page.pageIndex(); index <= page.pageCount(); ++index) {
          page.items().forEach(message -> {
            LOG.debug(
              "{} {} {}",
              message.time(),
              message.type(),
              message.message()
            );
          });
          page = paged.pageNext(transaction);
        }
      }
    }
  }

  private NPAssignmentExecutionStateType retrieveState(
    final NPAssignmentServiceType.NPExecutionInProgress inProgress)
    throws NPDatabaseException
  {
    try (var connection = this.database.openConnection(NPDatabaseRole.NORTHPIKE)) {
      try (var transaction = connection.openTransaction()) {
        return transaction.queries(AssignmentExecutionGetType.class)
          .execute(inProgress.executionId())
          .orElseThrow();
      }
    }
  }
}
