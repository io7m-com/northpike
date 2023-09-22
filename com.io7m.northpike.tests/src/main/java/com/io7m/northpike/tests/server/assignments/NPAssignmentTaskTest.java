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
import com.io7m.northpike.assignments.NPAssignment;
import com.io7m.northpike.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateCreated;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateCreationFailed;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateFailed;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateRequested;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateRunning;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateSucceeded;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType;
import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentWorkItem;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPKey;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.plans.NPPlanException;
import com.io7m.northpike.plans.NPPlanTimeouts;
import com.io7m.northpike.plans.NPPlanToolExecution;
import com.io7m.northpike.plans.NPPlanType;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemAccepted;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemStatusChanged;
import com.io7m.northpike.server.internal.assignments.NPAssignmentExecutionStatusChanged;
import com.io7m.northpike.server.internal.assignments.NPAssignmentTask;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.containers.NPTestContainerInstances;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.northpike.toolexec.NPTXFormats;
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

import java.net.URI;
import java.nio.file.Path;
import java.time.Duration;
import java.time.temporal.ChronoUnit;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.model.NPWorkItemStatus.WORK_ITEM_FAILED;
import static com.io7m.northpike.model.NPWorkItemStatus.WORK_ITEM_SUCCEEDED;
import static java.lang.Boolean.FALSE;
import static java.lang.Boolean.TRUE;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.mockito.ArgumentMatchers.any;

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
      NPTXFormats.nptx1(),
      """
        <?xml version="1.0" encoding="UTF-8" ?>
        <ToolExecution xmlns="urn:com.io7m.northpike.toolexec:1"
                       Name="run"
                       Version="1"></ToolExecution>
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

  private static NPAssignmentFixture ASSIGNMENT_FIXTURE;
  private static NPTestContainers.NPDatabaseFixture DATABASE_FIXTURE;
  private ScheduledExecutorService executor;
  private AtomicBoolean running;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers,
    final @TempDir Path reposDirectory)
    throws Exception
  {
    DATABASE_FIXTURE =
      NPTestContainerInstances.database(containers);
    ASSIGNMENT_FIXTURE =
      NPAssignmentFixture.create(DATABASE_FIXTURE, reposDirectory);
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

  @BeforeEach
  public void setup(
    final CloseableResourcesType closeables)
    throws Exception
  {
    ASSIGNMENT_FIXTURE.reset(closeables);
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
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(createPlanEmptyTask());

    Mockito.when(
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
        ASSIGNMENT_FIXTURE.commit().commitId()
      ),
      UUID.randomUUID()
    )) {
      task.run();
    }

    assertInstanceOf(
      NPAssignmentExecutionStateRequested.class,
      assertEventStatusChanged()
    );
    assertInstanceOf(
      NPAssignmentExecutionStateCreated.class,
      assertEventStatusChanged()
    );
    assertInstanceOf(
      NPAssignmentExecutionStateRunning.class,
      assertEventStatusChanged()
    );
    assertInstanceOf(
      NPAssignmentExecutionStateSucceeded.class,
      assertEventStatusChanged()
    );
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
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(createPlanOneTask());

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    Mockito.when(
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
        ASSIGNMENT_FIXTURE.commit().commitId()
      ),
      UUID.randomUUID()
    )) {

      /*
       * Schedule a task executed after an offer of work is made.
       */

      this.executor.schedule(() -> {
        try {
          offerAcceptLatch.await(5L, TimeUnit.SECONDS);
        } catch (final InterruptedException e) {
          Thread.currentThread().interrupt();
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
          Thread.currentThread().interrupt();
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
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(createPlanOneTask());

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    Mockito.when(
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
        ASSIGNMENT_FIXTURE.commit().commitId()
      ),
      UUID.randomUUID()
    )) {

      /*
       * Schedule a task executed after an offer of work is made.
       */

      this.executor.schedule(() -> {
        try {
          offerAcceptLatch.await(5L, TimeUnit.SECONDS);
        } catch (final InterruptedException e) {
          Thread.currentThread().interrupt();
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
          Thread.currentThread().interrupt();
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
        createPlanOneTimeoutAgentSelectionTask0()
      );

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    Mockito.when(
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
        ASSIGNMENT_FIXTURE.commit().commitId()
      ),
      UUID.randomUUID()
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
        createPlanOneTimeoutAgentSelectionTask1()
      );

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    Mockito.when(
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
        ASSIGNMENT_FIXTURE.commit().commitId()
      ),
      UUID.randomUUID()
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
        createPlanOneTimeoutAgentExecutionTask0()
      );

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    Mockito.when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .offerWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    Mockito.when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .sendWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commit().commitId()
      ),
      UUID.randomUUID()
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
        createPlanOneTimeoutAgentExecutionTask1()
      );

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    Mockito.when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .offerWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    Mockito.when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .sendWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commit().commitId()
      ),
      UUID.randomUUID()
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
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(createPlanThreeTaskSameAgent());

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    ASSIGNMENT_FIXTURE.transaction()
      .queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
        Map.of(),
        Map.of(),
        Map.of()
      ));

    ASSIGNMENT_FIXTURE.transaction()
      .commit();

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    Mockito.when(
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
        ASSIGNMENT_FIXTURE.commit().commitId()
      ),
      UUID.randomUUID()
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
            Thread.currentThread().interrupt();
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
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(plan);

    final var transaction = ASSIGNMENT_FIXTURE.transaction();
    transaction.queries(NPDatabaseQueriesPlansType.PutType.class)
      .execute(new NPDatabaseQueriesPlansType.PutType.Parameters(
        plan,
        new NPGarbageSerializers()
      ));

    final var agent =
      NPAgentID.of(UUID.randomUUID().toString());

    transaction.queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
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
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(createPlanOneTask());

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
      .queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
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
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(createPlanOneTask());

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
      .queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
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
      ASSIGNMENT_FIXTURE.createAssignmentWithPlan(createPlanOneTask());

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
      .queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(new NPAgentDescription(
        agent,
        "Agent",
        NPKey.generate(),
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

  private static void runSimpleFailure(
    final NPAssignment assignment,
    final NPAgentID agent,
    final Class<? extends NPAssignmentExecutionStateType> expected)
  {
    Mockito.when(
      ASSIGNMENT_FIXTURE.mockArchiveService()
        .linksForArchive(any())
    ).thenReturn(
      new NPArchiveLinks(
        URI.create("https://www.example.com/file.tgz"),
        URI.create("https://www.example.com/file.tgz.sha256")
      )
    );

    Mockito.when(
      ASSIGNMENT_FIXTURE.mockAgentService()
        .findSuitableAgentsFor(any(), any())
    ).thenReturn(
      new NPAgentServiceType.NPSuitableAgents(
        Set.of(agent),
        Set.of(agent)
      )
    );

    Mockito.when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .offerWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    Mockito.when(
      Boolean.valueOf(
        ASSIGNMENT_FIXTURE.mockAgentService()
          .sendWorkItem(any(), any())
      )
    ).thenReturn(TRUE);

    try (var task = NPAssignmentTask.create(
      ASSIGNMENT_FIXTURE.services(),
      new NPAssignmentExecutionRequest(
        assignment.name(),
        ASSIGNMENT_FIXTURE.commit().commitId()
      ),
      UUID.randomUUID()
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
}
