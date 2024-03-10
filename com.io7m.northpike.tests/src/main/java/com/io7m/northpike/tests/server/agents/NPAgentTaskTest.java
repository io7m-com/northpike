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


package com.io7m.northpike.tests.server.agents;

import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.ervilla.test_extension.ErvillaCloseAfterSuite;
import com.io7m.ervilla.test_extension.ErvillaConfiguration;
import com.io7m.ervilla.test_extension.ErvillaExtension;
import com.io7m.lanark.core.RDottedName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.clock.NPClock;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesSCMProvidersType;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.postgres.NPPGDatabases;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPAuditUserOrAgentType;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitGraph;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.NPToolExecutionEvaluated;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.NPWorkItemStatus;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPairEd448Type;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicEd448Type;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeCompletion;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentExecution;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreated;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.plans.NPPlanName;
import com.io7m.northpike.model.plans.NPPlanType;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.parsers.NPPlanSerializers;
import com.io7m.northpike.protocol.agent.NPACommandCEnvironmentInfo;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPACommandCLoginComplete;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemFailed;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemOutput;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemStarted;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemSucceeded;
import com.io7m.northpike.protocol.agent.NPACommandSWorkOffered;
import com.io7m.northpike.protocol.agent.NPACommandSWorkSent;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseError;
import com.io7m.northpike.protocol.agent.NPAResponseLoginChallenge;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.protocol.agent.NPAResponseWorkOffered;
import com.io7m.northpike.protocol.agent.NPAResponseWorkSent;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.intro.NPIMessageType;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.server.internal.agents.NPAgentAuthenticated;
import com.io7m.northpike.server.internal.agents.NPAgentTask;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemAccepted;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemStatusChanged;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.events.NPEventService;
import com.io7m.northpike.server.internal.metrics.NPMetricsServiceType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.tests.NPEventInterceptingService;
import com.io7m.northpike.tests.NPFakeSocket;
import com.io7m.northpike.tests.containers.NPDatabaseFixture;
import com.io7m.northpike.tests.containers.NPFixtures;
import com.io7m.northpike.tests.plans.NPFakeClock;
import com.io7m.northpike.tests.server.NPServerConfigurations;
import com.io7m.repetoir.core.RPServiceDirectory;
import com.io7m.verona.core.Version;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.apache.commons.io.input.QueueInputStream;
import org.apache.commons.io.output.QueueOutputStream;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mockito;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedInputStream;
import java.io.EOFException;
import java.io.IOException;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.net.URI;
import java.time.OffsetDateTime;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPCleanImmediately.CLEAN_IMMEDIATELY;
import static com.io7m.northpike.model.NPFailureFail.FAIL;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorApiMisuse;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.NPWorkItemStatus.WORK_ITEM_ACCEPTED;
import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
@Timeout(10L)
public final class NPAgentTaskTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentTaskTest.class);

  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();
  private static final NPA1Messages NPA1_MESSAGES =
    new NPA1Messages();
  private static final NPIProtocol NPA_1 =
    new NPIProtocol(NPA1Messages.protocolId(), 1L);

  private static final int LIMIT = 1_000_000;

  private static NPAgentKeyPairEd448Type KEY_PAIR_0;
  private static NPAgentKeyPairEd448Type KEY_PAIR_1;
  private static NPAgentKeyPairEd448Type KEY_PAIR_U;
  private static NPAgentKeyPublicEd448Type KEY_0;
  private static NPAgentKeyPublicEd448Type KEY_1;
  private static NPAgentKeyPublicEd448Type KEY_U;
  private static NPDatabaseFixture DATABASE_FIXTURE;

  private ExecutorService executor;
  private NPAgentDescription agent0;
  private NPAgentTask task;
  private NPConfigurationServiceType configuration;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPDatabaseType database;
  private NPEventInterceptingService events;
  private NPFakeClock clock;
  private NPMetricsServiceType metrics;
  private NPStrings strings;
  private NPTelemetryNoOp telemetry;
  private RPServiceDirectory services;
  private NPFakeSocket socket;
  private NPRepositoryDescription repository;
  private NPPlanType plan;
  private NPAssignment assignment;
  private NPCommit commit;
  private NPWorkItem workItem0;
  private NPWorkItemIdentifier workItem0Id;
  private NPAgentWorkItem agentWorkItem0;
  private NPAgentDescription agent1;
  private NPAssignmentExecutionStateType assignmentExecution;
  private PipedInputStream socketInputOnServerSide;
  private PipedOutputStream socketOutputOnServerSide;
  private PipedInputStream socketInputOnClientSide;
  private PipedOutputStream socketOutputOnClientSide;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers)
    throws Exception
  {
    DATABASE_FIXTURE = NPFixtures.database(containers);

    final var ed448 = new NPAgentKeyPairFactoryEd448();
    KEY_PAIR_0 = ed448.generateKeyPair();
    KEY_PAIR_1 = ed448.generateKeyPair();
    KEY_PAIR_U = ed448.generateKeyPair();
    KEY_0 = KEY_PAIR_0.publicKey();
    KEY_1 = KEY_PAIR_1.publicKey();
    KEY_U = KEY_PAIR_U.publicKey();
  }

  @BeforeEach
  public void setup(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers,
    final CloseableResourcesType closeables)
    throws Exception
  {
    DATABASE_FIXTURE.reset();

    this.database =
      closeables.addPerTestResource(DATABASE_FIXTURE.createDatabase());
    this.connection =
      closeables.addPerTestResource(this.database.openConnection(NORTHPIKE));
    this.transaction =
      closeables.addPerTestResource(this.connection.openTransaction());

    final var user = NPFixtures.idstore(containers).userWithLogin();
    this.transaction.setOwner(new NPAuditUserOrAgentType.User(user.id()));

    this.executor =
      Executors.newCachedThreadPool(r -> {
        final var thread = new Thread(r);
        thread.setName("AgentTaskTestThread-" + thread.threadId());
        thread.setDaemon(true);
        return thread;
      });

    this.services =
      new RPServiceDirectory();

    this.configuration =
      Mockito.mock(NPConfigurationServiceType.class);

    this.strings =
      NPStrings.create(Locale.ROOT);

    Mockito.when(this.configuration.configuration())
      .thenReturn(NPServerConfigurations.createFakeServerConfiguration(
        this.strings,
        new NPPGDatabases()
      ));

    this.clock =
      new NPFakeClock();
    this.telemetry =
      NPTelemetryNoOp.noop();
    this.events =
      new NPEventInterceptingService(NPEventService.create(this.telemetry));
    this.metrics =
      Mockito.mock(NPMetricsServiceType.class);

    this.services.register(
      NPStrings.class, this.strings);
    this.services.register(
      NPConfigurationServiceType.class, this.configuration);
    this.services.register(
      NPDatabaseType.class, this.database);
    this.services.register(
      NPEventServiceType.class, this.events);
    this.services.register(
      NPTelemetryServiceType.class, this.telemetry);
    this.services.register(
      NPClockServiceType.class, new NPClock(new NPFakeClock()));

    this.agent0 =
      new NPAgentDescription(
        new NPAgentID(UUID.fromString("00000000-0000-0000-0000-000000000000")),
        "Agent 0",
        KEY_0,
        Map.of(),
        Map.of(),
        Map.of()
      );

    this.agent1 =
      new NPAgentDescription(
        new NPAgentID(UUID.fromString("11111111-1111-1111-1111-000000000000")),
        "Agent 1",
        KEY_1,
        Map.of(),
        Map.of(),
        Map.of()
      );

    assertNotEquals(this.agent0.publicKey(), this.agent1.publicKey());

    this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class)
      .execute(new NPUser(user.id(), user.idName(), new MSubject(Set.of())));

    this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(this.agent0);

    this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class)
      .execute(this.agent1);

    this.repository =
      new NPRepositoryDescription(
        new RDottedName("x.y"),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com/repos"),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class)
      .execute(new NPSCMProviderDescription(
        this.repository.provider(),
        "SCM",
        URI.create("https://www.example.com/scm")
      ));

    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(this.repository);

    this.commit =
      new NPCommit(
        new NPCommitID(
          this.repository.id(),
          new NPCommitUnqualifiedID("adc83b19e793491b1c6ea0fd8b46cd9f32e592fc")
        ),
        OffsetDateTime.now(),
        OffsetDateTime.now(),
        new NPCommitAuthor("name", "email"),
        "Subject",
        "Body",
        Set.of(),
        Set.of()
      );

    this.transaction.queries(NPDatabaseQueriesRepositoriesType.CommitsPutType.class)
      .execute(new NPDatabaseQueriesRepositoriesType.CommitsPutType.Parameters(
        Set.of(this.commit),
        NPCommitGraph.create(Set.of())
      ));

    this.plan =
      NPPlans.builder(this.strings, NPPlanName.of("some.plan"), 1L)
        .build();

    this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class)
      .execute(new NPDatabaseQueriesPlansType.PutType.Parameters(
        this.plan,
        new NPPlanSerializers()
      ));

    this.assignment =
      new NPAssignment(
        NPAssignmentName.of("some.assignment"),
        this.repository.id(),
        this.plan.identifier(),
        NPAssignmentScheduleNone.SCHEDULE_NONE
      );

    this.transaction.queries(NPDatabaseQueriesAssignmentsType.PutType.class)
      .execute(this.assignment);

    this.assignmentExecution =
      new NPAssignmentExecutionStateCreated(
        OffsetDateTime.now(),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          this.assignment,
          this.commit.id().commitId()
        )
      );

    this.transaction.queries(NPDatabaseQueriesAssignmentsType.ExecutionPutType.class)
      .execute(this.assignmentExecution);

    this.workItem0Id =
      new NPWorkItemIdentifier(
        this.assignmentExecution.id(),
        new RDottedName("some.task")
      );

    this.agentWorkItem0 =
      new NPAgentWorkItem(
        this.workItem0Id,
        Map.of(),
        Set.of(),
        new NPToolExecutionEvaluated(
          new NPToolReference(
            NPToolReferenceName.of("x"),
            NPToolName.of("maven"),
            Version.of(1, 0, 0)
          ),
          Map.of(),
          List.of()
        ),
        new NPArchiveLinks(
          URI.create("http://www.example.com/file.tar.gz"),
          URI.create("http://www.example.com/file.tar.gz.sha256")
        ),
        Set.of(),
        FAIL,
        CLEAN_IMMEDIATELY
      );

    this.workItem0 =
      new NPWorkItem(
        this.workItem0Id,
        Optional.empty(),
        NPWorkItemStatus.WORK_ITEM_CREATED
      );

    this.transaction.queries(NPDatabaseQueriesAssignmentsType.WorkItemPutType.class)
      .execute(this.workItem0);

    this.transaction.commit();

    /*
     * Socket output on server side |-> socket input on client side.
     * Socket output on client side |-> socket input on server side.
     */

    this.socketInputOnServerSide =
      new PipedInputStream();
    this.socketOutputOnServerSide =
      new PipedOutputStream();

    this.socketInputOnClientSide =
      new PipedInputStream();
    this.socketOutputOnClientSide =
      new PipedOutputStream();

    this.socket =
      new NPFakeSocket(
        this.socketInputOnServerSide,
        this.socketOutputOnServerSide
      );

    this.socketOutputOnClientSide.connect(this.socketInputOnServerSide);
    this.socketOutputOnServerSide.connect(this.socketInputOnClientSide);

    /*
     * The server writes the available protocols, so the client
     * selects one here.
     */

    NPI_MESSAGES.writeLengthPrefixed(this.socketOutputOnClientSide, NPA_1);
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.task.close();
    this.executor.shutdown();
  }

  /**
   * An agent can authenticate.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentAuthenticates()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();
  }

  /**
   * Command requires authentication.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentNotAuthenticated0()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);

    this.receiveNPI(NPIProtocolsAvailable.class);
    this.receiveNPI(NPIProtocol.class);

    final var cmd0 = new NPACommandCLogin(randomUUID(), KEY_U);
    this.send(cmd0);
    final var error = this.receive(NPAResponseError.class);
    assertEquals(errorAuthentication(), error.errorCode());
  }

  /**
   * Command requires authentication.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentNotAuthenticated1()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);

    this.receiveNPI(NPIProtocolsAvailable.class);
    this.receiveNPI(NPIProtocol.class);

    final var cmd0 =
      new NPACommandCEnvironmentInfo(randomUUID(), Map.of(), Map.of());
    this.send(cmd0);
    final var error = this.receive(NPAResponseError.class);
    assertEquals(errorAuthentication(), error.errorCode());
  }

  /**
   * An agent can accept offered tasks.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentTaskOffered0()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.offerWorkItem(this.agentWorkItem0);
    });

    final var work =
      this.receive(NPACommandSWorkOffered.class);

    assertEquals(this.agentWorkItem0.identifier(), work.workItem());

    this.send(new NPAResponseWorkOffered(
      randomUUID(),
      work.messageID(),
      work.workItem(),
      true
    ));

    final var eventQueue = this.events.eventQueue();
    assertInstanceOf(NPAgentAuthenticated.class, eventQueue.poll());
    assertNull(eventQueue.poll());
  }

  /**
   * An agent can accept offered tasks.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentTaskOffered1()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.offerWorkItem(this.agentWorkItem0);
    });

    final var work =
      this.receive(NPACommandSWorkOffered.class);

    assertEquals(this.agentWorkItem0.identifier(), work.workItem());

    this.send(new NPAResponseWorkOffered(
      randomUUID(),
      work.messageID(),
      work.workItem(),
      false
    ));
  }

  /**
   * An agent closing a connection is an error.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentTaskOfferedError0()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.offerWorkItem(this.agentWorkItem0);
    });

    Thread.sleep(1_000L);

    this.socketInputOnClientSide.close();
  }

  /**
   * Responding to a "work offered" command with the wrong type of response
   * is an error.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentTaskOfferedResponseError()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.offerWorkItem(this.agentWorkItem0);
    });

    final var work =
      this.receive(NPACommandSWorkOffered.class);

    this.send(new NPAResponseOK(
      randomUUID(),
      work.messageID()
    ));
  }

  /**
   * An agent can perform sent tasks.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentTaskSent0()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.sendWorkItem(this.agentWorkItem0);
    });

    final var work =
      this.receive(NPACommandSWorkSent.class);

    assertEquals(this.agentWorkItem0, work.workItem());

    this.send(new NPAResponseWorkSent(
      randomUUID(),
      work.messageID(),
      work.workItem().identifier(),
      true
    ));

    this.send(new NPACommandCEnvironmentInfo(randomUUID(), Map.of(), Map.of()));
    this.receive(NPAResponseOK.class);

    final var eventQueue = this.events.eventQueue();
    assertInstanceOf(NPAgentAuthenticated.class, eventQueue.poll());
    assertInstanceOf(NPAgentWorkItemAccepted.class, eventQueue.poll());
    assertNull(eventQueue.poll());
  }

  /**
   * An agent can perform sent tasks.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentTaskSent1()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.sendWorkItem(this.agentWorkItem0);
    });

    final var work =
      this.receive(NPACommandSWorkSent.class);

    assertEquals(this.agentWorkItem0, work.workItem());

    this.send(new NPAResponseWorkSent(
      randomUUID(),
      work.messageID(),
      work.workItem().identifier(),
      false
    ));

    final var eventQueue = this.events.eventQueue();
    assertInstanceOf(NPAgentAuthenticated.class, eventQueue.poll());
    assertNull(eventQueue.poll());
  }

  /**
   * Responding to a "work sent" command with the wrong type of response
   * is an error.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentTaskSentResponseError()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.sendWorkItem(this.agentWorkItem0);
    });

    final var work =
      this.receive(NPACommandSWorkSent.class);

    assertEquals(this.agentWorkItem0, work.workItem());

    this.send(new NPAResponseOK(
      randomUUID(),
      work.messageID()
    ));
  }

  /**
   * An agent closing a connection is an error.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentTaskSentError0()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.sendWorkItem(this.agentWorkItem0);
    });

    Thread.sleep(1_000L);

    this.socketInputOnClientSide.close();
  }

  /**
   * An agent can report task statuses.
   *
   * @throws Exception On errors
   */

  @Test
  @Timeout(20L)
  public void testAgentTaskStatus0()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.sendWorkItem(this.agentWorkItem0);
    });

    final var work =
      this.receive(NPACommandSWorkSent.class);

    assertEquals(this.agentWorkItem0, work.workItem());

    this.send(new NPAResponseWorkSent(
      randomUUID(),
      work.messageID(),
      work.workItem().identifier(),
      true
    ));

    this.send(new NPACommandCWorkItemStarted(
      randomUUID(),
      work.workItem().identifier()
    ));

    this.receive(NPAResponseOK.class);

    this.send(new NPACommandCWorkItemOutput(
      randomUUID(),
      OffsetDateTime.now(),
      work.workItem().identifier(),
      Map.of("a", "x", "b", "y"),
      "OK!",
      Optional.of(NPStoredException.ofException(new IOException()))
    ));

    this.receive(NPAResponseOK.class);

    this.send(new NPACommandCWorkItemSucceeded(
      randomUUID(),
      work.workItem().identifier()
    ));

    this.receive(NPAResponseOK.class);

    final var eventQueue = this.events.eventQueue();
    assertInstanceOf(NPAgentAuthenticated.class, eventQueue.poll());
    assertInstanceOf(NPAgentWorkItemAccepted.class, eventQueue.poll());
    assertInstanceOf(NPAgentWorkItemStatusChanged.class, eventQueue.poll());
    assertInstanceOf(NPAgentWorkItemStatusChanged.class, eventQueue.poll());
    assertNull(eventQueue.poll());
  }

  /**
   * An agent can report task statuses.
   *
   * @throws Exception On errors
   */

  @Test
  @Timeout(20L)
  public void testAgentTaskStatus1()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.sendWorkItem(this.agentWorkItem0);
    });

    final var work =
      this.receive(NPACommandSWorkSent.class);

    assertEquals(this.agentWorkItem0, work.workItem());

    this.send(new NPAResponseWorkSent(
      randomUUID(),
      work.messageID(),
      work.workItem().identifier(),
      true
    ));

    this.send(new NPACommandCWorkItemStarted(
      randomUUID(),
      work.workItem().identifier()
    ));

    this.receive(NPAResponseOK.class);

    this.send(new NPACommandCWorkItemOutput(
      randomUUID(),
      OffsetDateTime.now(),
      work.workItem().identifier(),
      Map.of("a", "x", "b", "y"),
      "OK!",
      Optional.of(NPStoredException.ofException(new IOException()))
    ));

    this.receive(NPAResponseOK.class);

    this.send(new NPACommandCWorkItemFailed(
      randomUUID(),
      work.workItem().identifier()
    ));

    this.receive(NPAResponseOK.class);
  }

  /**
   * An agent cannot report task statuses for other agent's work items.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentTaskWorkItemNotMine()
    throws Exception
  {
    this.task = NPAgentTask.create(this.services, this.socket);
    this.executor.execute(this.task);
    this.authenticate();

    this.executor.execute(() -> {
      this.task.sendWorkItem(this.agentWorkItem0);
    });

    final var work =
      this.receive(NPACommandSWorkSent.class);

    assertEquals(this.agentWorkItem0, work.workItem());

    this.send(new NPAResponseWorkSent(
      randomUUID(),
      work.messageID(),
      work.workItem().identifier(),
      true
    ));

    /*
     * Verify that the server thinks that Agent 0 accepted the work.
     */

    while (true) {
      try (var t = this.connection.openTransaction()) {
        final var workItem =
          t.queries(NPDatabaseQueriesAssignmentsType.WorkItemGetType.class)
            .execute(this.workItem0.identifier())
            .orElseThrow();

        if (workItem.status() == WORK_ITEM_ACCEPTED) {
          assertEquals(this.agentWorkItem0.identifier(), workItem.identifier());
          assertEquals(Optional.of(this.agent0.id()), workItem.selectedAgent());
          break;
        }
      }
    }

    /*
     * Now change the work such that Agent 1 appears to have accepted the
     * work instead.
     */

    try (var t = this.connection.openTransaction()) {
      t.queries(NPDatabaseQueriesAssignmentsType.WorkItemPutType.class)
        .execute(
          new NPWorkItem(
            this.workItem0.identifier(),
            Optional.of(this.agent1.id()),
            WORK_ITEM_ACCEPTED
          )
        );
      t.commit();
    }

    /*
     * Now Agent 0 should receive an error upon trying to start the work.
     */

    this.send(new NPACommandCWorkItemStarted(
      randomUUID(),
      work.workItem().identifier()
    ));

    final var error = this.receive(NPAResponseError.class);
    assertEquals(errorApiMisuse(), error.errorCode());
  }

  private void authenticate()
    throws Exception
  {
    this.receiveNPI(NPIProtocolsAvailable.class);
    this.receiveNPI(NPIProtocol.class);

    final var cmd0 = new NPACommandCLogin(randomUUID(), KEY_0);
    this.send(cmd0);

    final var r0 =
      this.receive(NPAResponseLoginChallenge.class);

    final var signature =
      KEY_PAIR_0.signData(r0.challenge().data());

    final var cmd1 =
      new NPACommandCLoginComplete(
        randomUUID(),
        new NPAgentLoginChallengeCompletion(r0.challenge().id(), signature)
      );

    this.send(cmd1);
    this.receive(NPAResponseOK.class);

    final var cmd2 =
      new NPACommandCEnvironmentInfo(randomUUID(), Map.of(), Map.of());
    this.send(cmd2);
    this.receive(NPAResponseOK.class);

    LOG.debug("Authenticated!");
  }

  private <M extends NPAMessageType> M receive(
    final Class<M> clazz)
    throws Exception
  {
    final var m =
      NPA1_MESSAGES.readLengthPrefixed(
        this.strings,
        LIMIT,
        this.socketInputOnClientSide
      );

    LOG.debug("receive: {}", m);
    return clazz.cast(m);
  }

  private <M extends NPIMessageType> M receiveNPI(
    final Class<M> clazz)
    throws Exception
  {
    final var m =
      NPI_MESSAGES.readLengthPrefixed(
        this.strings,
        LIMIT,
        this.socketInputOnClientSide
      );

    LOG.debug("receiveNPI: {}", m);
    return clazz.cast(m);
  }

  private void send(
    final NPAMessageType message)
    throws Exception
  {
    NPA1_MESSAGES.writeLengthPrefixed(
      this.socketOutputOnClientSide,
      message
    );
  }
}
