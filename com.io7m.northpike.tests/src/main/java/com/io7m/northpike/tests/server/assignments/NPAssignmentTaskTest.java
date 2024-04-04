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
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPublicKeysType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.PublicKeyAssignType;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType;
import com.io7m.northpike.keys.NPPublicKeys;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPairEd448Type;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicEd448Type;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreated;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreationFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRequested;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRunning;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateSucceeded;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.model.plans.NPPlanTimeouts;
import com.io7m.northpike.model.plans.NPPlanToolExecution;
import com.io7m.northpike.model.plans.NPPlanType;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemAccepted;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemStatusChanged;
import com.io7m.northpike.server.internal.assignments.NPAssignmentExecutionStatusChanged;
import com.io7m.northpike.server.internal.assignments.NPAssignmentTask;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.containers.NPDatabaseFixture;
import com.io7m.northpike.tests.containers.NPFixtures;
import com.io7m.northpike.tests.keys.NPPublicKeysTest;
import com.io7m.verona.core.Version;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.api.io.TempDir;
import org.mockito.Mockito;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.nio.file.Path;
import java.time.Duration;
import java.time.temporal.ChronoUnit;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS;
import static com.io7m.northpike.model.NPWorkItemStatus.WORK_ITEM_FAILED;
import static com.io7m.northpike.model.NPWorkItemStatus.WORK_ITEM_SUCCEEDED;
import static java.lang.Boolean.FALSE;
import static java.lang.Boolean.TRUE;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.when;

@Timeout(value = 10L, unit = TimeUnit.SECONDS)
@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPAssignmentTaskTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAssignmentTaskTest.class);

  private static final NPStrings STRINGS = NPStrings.create(Locale.ROOT);

  private static final NPToolExecutionDescription TOOL_EXECUTION_DESCRIPTION =
    new NPToolExecutionDescription(
      NPToolExecutionIdentifier.of("run", 1L),
      NPToolName.of("tool"),
      "A description.",
      NPFormatName.of("com.io7m.northpike.toolexec.js"),
      """

        """);

  private static final NPToolReference TOOL_REFERENCE =
    new NPToolReference(
      NPToolReferenceName.of("t"),
      NPToolName.of("tool"),
      Version.of(1, 0, 0)
    );

  private static final NPPlanToolExecution TOOL_EXECUTION =
    new NPPlanToolExecution(
      NPToolReferenceName.of("t"),
      NPToolExecutionIdentifier.of("run", 1L),
      Set.of()
    );

  private static NPAgentKeyPublicEd448Type KEY;
  private static NPAgentKeyPairEd448Type KEY_PAIR;
  private static NPAssignmentFixture ASSIGNMENT_FIXTURE;
  private static NPDatabaseFixture DATABASE_FIXTURE;
  private ScheduledExecutorService executor;
  private AtomicBoolean running;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers,
    final @TempDir Path reposDirectory)
    throws Exception
  {
    DATABASE_FIXTURE =
      NPFixtures.database(NPFixtures.pod(containers));
    ASSIGNMENT_FIXTURE =
      NPAssignmentFixture.create(
        NPFixtures.idstore(NPFixtures.pod(containers)),
        DATABASE_FIXTURE,
        reposDirectory
      );

    KEY_PAIR = new NPAgentKeyPairFactoryEd448().generateKeyPair();
    KEY = KEY_PAIR.publicKey();
  }

  private static NPPlanType createPlanOneTask()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(STRINGS, "plans.one", 1L);

    final var transaction =
      ASSIGNMENT_FIXTURE.transaction();

    transaction.queries(NPDatabaseQueriesToolsType.PutExecutionDescriptionType.class)
      .execute(TOOL_EXECUTION_DESCRIPTION);

    transaction.commit();

    planBuilder.addToolReference(TOOL_REFERENCE);
    planBuilder.addTask("task0")
      .setToolExecution(TOOL_EXECUTION);

    return planBuilder.build();
  }

  private static NPPlanType createPlanEmptyTask()
    throws NPPlanException
  {
    return NPPlans.builder(STRINGS, "plans.empty", 1L)
      .build();
  }

  private static NPPlanType createPlanOneTimeoutAgentExecutionTask0()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(STRINGS, "plans.one", 1L);

    final var transaction =
      ASSIGNMENT_FIXTURE.transaction();

    transaction.queries(NPDatabaseQueriesToolsType.PutExecutionDescriptionType.class)
      .execute(TOOL_EXECUTION_DESCRIPTION);

    transaction.commit();

    planBuilder.addToolReference(TOOL_REFERENCE);
    planBuilder.addTask("task0")
      .setExecutionTimeout(Duration.of(1L, ChronoUnit.SECONDS))
      .setToolExecution(TOOL_EXECUTION);

    return planBuilder.build();
  }

  private static NPPlanType createPlanOneTimeoutAgentExecutionTask1()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(STRINGS, "plans.one", 1L);

    final var transaction =
      ASSIGNMENT_FIXTURE.transaction();

    transaction.queries(NPDatabaseQueriesToolsType.PutExecutionDescriptionType.class)
      .execute(TOOL_EXECUTION_DESCRIPTION);

    transaction.commit();

    planBuilder.setTimeouts(
      new NPPlanTimeouts(
        Duration.ofDays(365L),
        Duration.ofSeconds(1L)
      )
    );

    planBuilder.addToolReference(TOOL_REFERENCE);
    planBuilder.addTask("task0")
      .setToolExecution(TOOL_EXECUTION);

    return planBuilder.build();
  }

  private static NPPlanType createPlanOneTimeoutAgentSelectionTask0()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(STRINGS, "plans.one", 1L);

    final var transaction =
      ASSIGNMENT_FIXTURE.transaction();

    transaction.queries(NPDatabaseQueriesToolsType.PutExecutionDescriptionType.class)
      .execute(TOOL_EXECUTION_DESCRIPTION);

    transaction.commit();

    planBuilder.addToolReference(TOOL_REFERENCE);
    planBuilder.addTask("task0")
      .setAgentSelectionTimeout(Duration.of(1L, ChronoUnit.SECONDS))
      .setToolExecution(TOOL_EXECUTION);

    return planBuilder.build();
  }

  private static NPPlanType createPlanOneTimeoutAgentSelectionTask1()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(STRINGS, "plans.one", 1L);

    final var transaction =
      ASSIGNMENT_FIXTURE.transaction();

    transaction.queries(NPDatabaseQueriesToolsType.PutExecutionDescriptionType.class)
      .execute(TOOL_EXECUTION_DESCRIPTION);

    transaction.commit();

    planBuilder.addToolReference(TOOL_REFERENCE);
    planBuilder.addTask("task0")
      .setToolExecution(TOOL_EXECUTION);

    planBuilder.setTimeouts(
      new NPPlanTimeouts(
        Duration.ofSeconds(1L),
        Duration.ofSeconds(1L)
      )
    );
    return planBuilder.build();
  }

  private static NPAssignmentExecutionStateType assertEventStatusChanged()
  {
    return assertInstanceOf(
      NPAssignmentExecutionStatusChanged.class,
      ASSIGNMENT_FIXTURE.events().poll()
    ).execution();
  }

  private static void runSimpleFailure(
    final NPAssignment assignment,
    final NPAgentID agent,
    final Class<? extends NPAssignmentExecutionStateType> expected)
  {
    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .offerWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .sendWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());
    assertInstanceOf(expected, e.execution());
  }

  private static NPPlanType createPlanThreeTaskSameAgent()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(STRINGS, "plans.three", 1L);

    final var transaction =
      ASSIGNMENT_FIXTURE.transaction();

    transaction.queries(NPDatabaseQueriesToolsType.PutExecutionDescriptionType.class)
      .execute(TOOL_EXECUTION_DESCRIPTION);

    transaction.commit();

    planBuilder.addToolReference(TOOL_REFERENCE);

    final var t0 =
      planBuilder.addTask("task0")
        .setToolExecution(TOOL_EXECUTION);

    final var t1 =
      planBuilder.addTask("task1")
        .setToolExecution(TOOL_EXECUTION)
        .setAgentMustBeSameAs(t0);

    final var t2 =
      planBuilder.addTask("task2")
        .setToolExecution(TOOL_EXECUTION)
        .setAgentMustBeSameAs(t1);

    return planBuilder.build();
  }

  @BeforeEach
  public void setup(
    final CloseableResourcesType closeables)
    throws Exception
  {
    ASSIGNMENT_FIXTURE.reset(closeables);

    when(ASSIGNMENT_FIXTURE.mockRepositoryService().checkOne(any()))
      .thenReturn(CompletableFuture.completedFuture(null));

    this.running = new AtomicBoolean(true);
    this.executor = Executors.newScheduledThreadPool(1);
  }

  @AfterEach
  public void tearDown()
  {
    this.running.set(false);
    this.executor.shutdown();
  }

  /**
   * An empty plan succeeds immediately.
   *
   * @throws Exception On errors
   */

  @Test
  public void testEmptyPlanSucceeds()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS, createPlanEmptyTask());

    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    assertEventStatuses(
      NPAssignmentExecutionStateRequested.class,
      NPAssignmentExecutionStateCreated.class,
      NPAssignmentExecutionStateRunning.class,
      NPAssignmentExecutionStateSucceeded.class
    );
  }

  @SafeVarargs
  private static void assertEventStatuses(
    final Class<? extends NPAssignmentExecutionStateType>... expectedStates)
  {
    final var actualStates =
      List.copyOf(ASSIGNMENT_FIXTURE.events())
        .stream()
        .map(NPAssignmentExecutionStatusChanged.class::cast)
        .map(NPAssignmentExecutionStatusChanged::execution)
        .map(NPAssignmentExecutionStateType::getClass)
        .toList();

    final var expectedStateList =
      List.of(expectedStates);

    final var count =
      Math.max(actualStates.size(), expectedStateList.size());

    for (int index = 0; index < count; ++index) {
      Class<?> actual = null;
      Class<?> expected = null;
      if (index < actualStates.size()) {
        actual = actualStates.get(index);
      }
      if (index < expectedStateList.size()) {
        expected = expectedStateList.get(index);
      }

      final var line =
        String.format(
          "[%d] %-48s = %-48s",
          Integer.valueOf(index),
          expected.getSimpleName(),
          actual.getSimpleName()
        );

      LOG.debug("{}", line);
    }

    assertEquals(List.of(expectedStates), actualStates);
  }

  /**
   * A simple one-task plan succeeds if the agent executes fully.
   *
   * @throws Exception On errors
   */

  @Test
  public void testOneTaskPlanSucceeds()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS, createPlanOneTask());

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    final var offerAcceptLatch =
      new CountDownLatch(1);

    Mockito.doAnswer(invocationOnMock -> {
        LOG.debug("Offer latched...");
        offerAcceptLatch.countDown();
        return TRUE;
      })
      .when(ASSIGNMENT_FIXTURE.mockAgentService())
      .offerWorkItem(any(), any());

    final var sendLatch =
      new CountDownLatch(1);

    Mockito.doAnswer(invocationOnMock -> {
        LOG.debug("Send latched...");
        sendLatch.countDown();
        return TRUE;
      })
      .when(ASSIGNMENT_FIXTURE.mockAgentService())
      .sendWorkItem(any(), any());

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {

      /*
       * Schedule a task executed after an offer of work is made.
       */

      this.executor.schedule(() -> {
        try {
          offerAcceptLatch.await(5L, TimeUnit.SECONDS);
        } catch (final InterruptedException e) {
          throw new IllegalStateException(e);
        }

        final var events =
          ASSIGNMENT_FIXTURE.eventService();
        events.emit(new NPAgentWorkItemAccepted(
          agent,
          new NPWorkItemIdentifier(
            task.executionId(),
            new RDottedName("task0")
          )
        ));
      }, 1000L, TimeUnit.MILLISECONDS);

      /*
       * Schedule a task executed after work is accepted.
       */

      this.executor.schedule(() -> {
        try {
          sendLatch.await(5L, TimeUnit.SECONDS);
        } catch (final InterruptedException e) {
          throw new IllegalStateException(e);
        }

        final var events =
          ASSIGNMENT_FIXTURE.eventService();
        events.emit(new NPAgentWorkItemStatusChanged(
          agent,
          new NPWorkItemIdentifier(
            task.executionId(),
            new RDottedName("task0")
          ),
          WORK_ITEM_SUCCEEDED
        ));
      }, 2000L, TimeUnit.MILLISECONDS);

      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAgentWorkItemAccepted.class, eQ.poll());
    assertInstanceOf(NPAgentWorkItemStatusChanged.class, eQ.poll());
    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());

    assertInstanceOf(
      NPAssignmentExecutionStateSucceeded.class,
      e.execution()
    );
  }

  /**
   * A simple one-task plan fails if the agent fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testOneTaskPlanFails()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS, createPlanOneTask());

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    final var offerAcceptLatch =
      new CountDownLatch(1);

    Mockito.doAnswer(invocationOnMock -> {
        LOG.debug("Offer latched...");
        offerAcceptLatch.countDown();
        return TRUE;
      })
      .when(ASSIGNMENT_FIXTURE.mockAgentService())
      .offerWorkItem(any(), any());

    final var sendLatch =
      new CountDownLatch(1);

    Mockito.doAnswer(invocationOnMock -> {
        LOG.debug("Send latched...");
        sendLatch.countDown();
        return TRUE;
      })
      .when(ASSIGNMENT_FIXTURE.mockAgentService())
      .sendWorkItem(any(), any());

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {

      /*
       * Schedule a task executed after an offer of work is made.
       */

      this.executor.schedule(() -> {
        try {
          offerAcceptLatch.await(5L, TimeUnit.SECONDS);
        } catch (final InterruptedException e) {
          throw new IllegalStateException(e);
        }

        final var events =
          ASSIGNMENT_FIXTURE.eventService();
        events.emit(new NPAgentWorkItemAccepted(
          agent,
          new NPWorkItemIdentifier(
            task.executionId(),
            new RDottedName("task0")
          )
        ));
      }, 1000L, TimeUnit.MILLISECONDS);

      /*
       * Schedule a task executed after work is accepted.
       */

      this.executor.schedule(() -> {
        try {
          sendLatch.await(5L, TimeUnit.SECONDS);
        } catch (final InterruptedException e) {
          throw new IllegalStateException(e);
        }

        final var events =
          ASSIGNMENT_FIXTURE.eventService();
        events.emit(new NPAgentWorkItemStatusChanged(
          agent,
          new NPWorkItemIdentifier(
            task.executionId(),
            new RDottedName("task0")
          ),
          WORK_ITEM_FAILED
        ));
      }, 2000L, TimeUnit.MILLISECONDS);

      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAgentWorkItemAccepted.class, eQ.poll());
    assertInstanceOf(NPAgentWorkItemStatusChanged.class, eQ.poll());
    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());

    assertInstanceOf(
      NPAssignmentExecutionStateFailed.class,
      e.execution()
    );
  }

  /**
   * A simple one-task plan times out if no agent ever accepts work.
   *
   * @throws Exception On errors
   */

  @Test
  public void testOneTaskPlanTimeoutAgentSelection0()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS,
        createPlanOneTimeoutAgentSelectionTask0()
      );

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    Mockito.doAnswer(invocationOnMock -> {
        LOG.debug("Nobody home...");
        return FALSE;
      })
      .when(ASSIGNMENT_FIXTURE.mockAgentService())
      .offerWorkItem(any(), any());

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());

    assertInstanceOf(
      NPAssignmentExecutionStateFailed.class,
      e.execution()
    );
  }

  /**
   * A simple one-task plan times out if no agent ever accepts work.
   *
   * @throws Exception On errors
   */

  @Test
  public void testOneTaskPlanTimeoutAgentSelection1()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS,
        createPlanOneTimeoutAgentSelectionTask1()
      );

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    Mockito.doAnswer(invocationOnMock -> {
        LOG.debug("Nobody home...");
        return FALSE;
      })
      .when(ASSIGNMENT_FIXTURE.mockAgentService())
      .offerWorkItem(any(), any());

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());

    assertInstanceOf(
      NPAssignmentExecutionStateFailed.class,
      e.execution()
    );
  }

  /**
   * A simple one-task plan times out if the task takes too long.
   *
   * @throws Exception On errors
   */

  @Test
  public void testOneTaskPlanTimeoutAgentExecution0()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS,
        createPlanOneTimeoutAgentExecutionTask0()
      );

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .offerWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .sendWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());

    assertInstanceOf(
      NPAssignmentExecutionStateFailed.class,
      e.execution()
    );
  }

  /**
   * A simple one-task plan times out if the task takes too long.
   *
   * @throws Exception On errors
   */

  @Test
  public void testOneTaskPlanTimeoutAgentExecution1()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS,
        createPlanOneTimeoutAgentExecutionTask1()
      );

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .offerWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .sendWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());

    assertInstanceOf(
      NPAssignmentExecutionStateFailed.class,
      e.execution()
    );
  }

  /**
   * A simple three-task plan succeeds if the agent executes fully.
   *
   * @throws Exception On errors
   */

  @Test
  @Timeout(value = 10L)
  public void testThreeTaskPlanSameAgentSucceeds()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS, createPlanThreeTaskSameAgent());

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .offerWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    /*
     * Every time a work item is sent to the agent, put the work item
     * on the queue.
     */

    final var itemQueue =
      new LinkedBlockingQueue<NPAgentWorkItem>();

    Mockito.doAnswer(invocationOnMock -> {
        final var item = invocationOnMock.getArgument(1);
        LOG.debug("Adding work item {} to queue", item);
        itemQueue.add((NPAgentWorkItem) item);
        return TRUE;
      })
      .when(ASSIGNMENT_FIXTURE.mockAgentService())
      .sendWorkItem(any(), any());

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitUnsigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {

      /*
       * Schedule a task that pulls work items off the queue and submits
       * an event that claims that execution succeeded.
       */

      this.executor.execute(() -> {
        while (this.running.get()) {
          LOG.debug("Waiting for work item...");

          NPAgentWorkItem item = null;
          try {
            item = itemQueue.poll(1L, TimeUnit.SECONDS);
          } catch (final InterruptedException e) {
            throw new IllegalStateException(e);
          }

          if (item == null) {
            LOG.debug("No work item yet.");
            continue;
          }

          final var events =
            ASSIGNMENT_FIXTURE.eventService();

          LOG.debug("Claiming work item {} succeeded", item);
          events.emit(new NPAgentWorkItemStatusChanged(
            agent,
            item.identifier(),
            WORK_ITEM_SUCCEEDED
          ));
        }
      });

      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAgentWorkItemStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAgentWorkItemStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAgentWorkItemStatusChanged.class, eQ.poll());
    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());

    assertInstanceOf(
      NPAssignmentExecutionStateSucceeded.class,
      e.execution()
    );
  }

  /**
   * An unparseable plan fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanInvalid0()
    throws Exception
  {
    final var plan =
      createPlanOneTask();
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(ALLOW_UNSIGNED_COMMITS, plan);

    final var transaction = ASSIGNMENT_FIXTURE.transaction();
    transaction.queries(NPDatabaseQueriesPlansType.PlanPutType.class)
      .execute(new NPDatabaseQueriesPlansType.PlanPutType.Parameters(
        plan,
        new NPGarbageSerializers()
      ));

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    transaction.queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    transaction.commit();
    runSimpleFailure(
      assignment,
      agent,
      NPAssignmentExecutionStateCreationFailed.class
    );
  }

  /**
   * A plan with an unparseable tool execution fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanToolExecutionInvalid0()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS, createPlanOneTask());

    final var transaction = ASSIGNMENT_FIXTURE.transaction();
    transaction.queries(NPDatabaseQueriesToolsType.PutExecutionDescriptionType.class)
      .execute(new NPToolExecutionDescription(
        TOOL_EXECUTION_DESCRIPTION.identifier(),
        TOOL_EXECUTION_DESCRIPTION.tool(),
        TOOL_EXECUTION_DESCRIPTION.description(),
        TOOL_EXECUTION_DESCRIPTION.format(),
        """
          <?xml version="1.0" encoding="UTF-8" ?>
          <ToolExecution xmlns="urn:com.io7m.northpike.toolexec:1"
                         Name="run"
                         Version="1">
            <What/>
            <Else/>
          </ToolExecution>
                         """
      ));

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    transaction
      .queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    transaction.commit();
    runSimpleFailure(
      assignment,
      agent,
      NPAssignmentExecutionStateCreationFailed.class
    );
  }

  /**
   * A plan with an ill-typed tool execution fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanToolExecutionInvalid1()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS, createPlanOneTask());

    final var transaction = ASSIGNMENT_FIXTURE.transaction();
    transaction.queries(NPDatabaseQueriesToolsType.PutExecutionDescriptionType.class)
      .execute(new NPToolExecutionDescription(
        TOOL_EXECUTION_DESCRIPTION.identifier(),
        TOOL_EXECUTION_DESCRIPTION.tool(),
        TOOL_EXECUTION_DESCRIPTION.description(),
        TOOL_EXECUTION_DESCRIPTION.format(),
        """
          <?xml version="1.0" encoding="UTF-8" ?>
          <ToolExecution xmlns="urn:com.io7m.northpike.toolexec:1"
                         Name="run"
                         Version="1">
            <If>
              <Condition>
                <IsEqual>
                  <Number Value="23"/>
                  <String Value="x"/>
                </IsEqual>
              </Condition>
              <Then>
                <ArgumentAdd Value="ok"/>
              </Then>
            </If>
          </ToolExecution>
                         """
      ));

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    transaction
      .queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    transaction.commit();
    runSimpleFailure(
      assignment,
      agent,
      NPAssignmentExecutionStateCreationFailed.class
    );
  }

  /**
   * A plan with an unsupported tool execution fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanToolExecutionInvalid2()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        ALLOW_UNSIGNED_COMMITS, createPlanOneTask());

    final var transaction = ASSIGNMENT_FIXTURE.transaction();
    transaction.queries(NPDatabaseQueriesToolsType.PutExecutionDescriptionType.class)
      .execute(new NPToolExecutionDescription(
        TOOL_EXECUTION_DESCRIPTION.identifier(),
        TOOL_EXECUTION_DESCRIPTION.tool(),
        TOOL_EXECUTION_DESCRIPTION.description(),
        NPFormatName.of("x.y.z"),
        TOOL_EXECUTION_DESCRIPTION.text()
      ));

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    transaction
      .queries(NPDatabaseQueriesAgentsType.AgentPutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        KEY,
        Map.of(),
        Map.of(),
        Map.of()
      ));

    transaction.commit();
    runSimpleFailure(
      assignment,
      agent,
      NPAssignmentExecutionStateCreationFailed.class
    );
  }

  /**
   * The plan fails if commit signing is required but the commit is signed
   * with an unknown key.
   *
   * @throws Exception On errors
   */

  @Test
  @Timeout(value = 10L)
  public void testCommitWithUnknownKey()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY, createPlanEmptyTask());

    when(
      ASSIGNMENT_FIXTURE.mockRepositoryService()
        .verifyCommitSignature(any(), any())
    ).thenReturn(CompletableFuture.failedFuture(
      new IOException("Wrong signature.")
    ));

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitSigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());

    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());
    assertInstanceOf(NPAssignmentExecutionStateCreationFailed.class, e.execution());
  }

  /**
   * The plan fails if commit signing is required but the commit is signed
   * with an unknown key.
   *
   * @throws Exception On errors
   */

  @Test
  @Timeout(value = 10L)
  public void testCommitWithUnknownKeySpecific()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS, createPlanEmptyTask());

    when(
      ASSIGNMENT_FIXTURE.mockRepositoryService()
        .verifyCommitSignature(any(), any())
    ).thenReturn(CompletableFuture.failedFuture(
      new IOException("Wrong signature.")
    ));

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitSignedSpecific().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());

    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());
    assertInstanceOf(NPAssignmentExecutionStateCreationFailed.class, e.execution());
  }

  /**
   * The plan fails if commit signing is required but the commit is signed
   * with a key that isn't assigned to the repository.
   *
   * @throws Exception On errors
   */

  @Test
  @Timeout(value = 10L)
  public void testCommitWithKeySpecificNotAssigned()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS, createPlanEmptyTask());

    when(
      ASSIGNMENT_FIXTURE.mockRepositoryService()
        .verifyCommitSignature(any(), any())
    ).thenReturn(CompletableFuture.completedFuture(
      new NPFingerprint("a438a737c771787195cfc166f84351f72c918476")
    ));

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitSignedSpecific().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    final var eQ = ASSIGNMENT_FIXTURE.events();
    assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());

    final var e =
      assertInstanceOf(NPAssignmentExecutionStatusChanged.class, eQ.poll());
    assertEquals(0, eQ.size());
    assertInstanceOf(NPAssignmentExecutionStateCreationFailed.class, e.execution());
  }

  /**
   * A commit that requires signing with a known key succeeds if the commit
   * is signed with a known key.
   *
   * @throws Exception On errors
   */

  @Test
  public void testCommitSignedSucceeds()
    throws Exception
  {
    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY, createPlanEmptyTask());

    when(
      ASSIGNMENT_FIXTURE.mockRepositoryService()
        .verifyCommitSignature(any(), any())
    ).thenReturn(CompletableFuture.completedFuture(
      new NPFingerprint("a438a737c771787195cfc166f84351f72c918476")
    ));

    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitSigned().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    assertEventStatuses(
      NPAssignmentExecutionStateRequested.class,
      NPAssignmentExecutionStateCreated.class,
      NPAssignmentExecutionStateRunning.class,
      NPAssignmentExecutionStateSucceeded.class
    );
  }

  /**
   * A commit that requires signing with a specific key succeeds if the commit
   * is signed with a specific key.
   *
   * @throws Exception On errors
   */

  @Test
  public void testCommitSignedSpecificSucceeds()
    throws Exception
  {
    final var transaction =
      ASSIGNMENT_FIXTURE.transaction();

    transaction.queries(NPDatabaseQueriesPublicKeysType.PutType.class)
      .execute(
        NPPublicKeys.decode(resource("key-pub-0.asc")).get(0)
      );

    transaction.queries(PublicKeyAssignType.class)
      .execute(new PublicKeyAssignType.Parameters(
        ASSIGNMENT_FIXTURE.commitSignedSpecific().repository(),
        new NPFingerprint("a438a737c771787195cfc166f84351f72c918476")
      ));

    transaction.commit();

    final var assignment =
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(
        REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS, createPlanEmptyTask());

    when(
      ASSIGNMENT_FIXTURE.mockRepositoryService()
        .verifyCommitSignature(any(), any())
    ).thenReturn(CompletableFuture.completedFuture(
      new NPFingerprint("a438a737c771787195cfc166f84351f72c918476")
    ));

    when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commitSignedSpecific().commitId()
      ),
      new NPAssignmentExecutionID(UUID.randomUUID())
    )) {
      task.run();
    }

    assertEventStatuses(
      NPAssignmentExecutionStateRequested.class,
      NPAssignmentExecutionStateCreated.class,
      NPAssignmentExecutionStateRunning.class,
      NPAssignmentExecutionStateSucceeded.class
    );
  }

  private static InputStream resource(
    final String name)
  {
    return NPPublicKeysTest.class
      .getResourceAsStream("/com/io7m/northpike/tests/" + name);
  }
}
