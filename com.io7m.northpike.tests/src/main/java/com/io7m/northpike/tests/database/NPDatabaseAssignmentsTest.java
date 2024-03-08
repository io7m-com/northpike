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

package com.io7m.northpike.tests.database;

import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.ervilla.test_extension.ErvillaCloseAfterSuite;
import com.io7m.ervilla.test_extension.ErvillaConfiguration;
import com.io7m.ervilla.test_extension.ErvillaExtension;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionDeleteType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionDeleteType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionLogAddType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionLogListType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionPutType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionSearchType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionWorkItemsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.WorkItemGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.WorkItemLogAddType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.WorkItemPutType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.CommitsPutType;
import com.io7m.northpike.database.api.NPDatabaseQueriesSCMProvidersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitGraph;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.NPWorkItemLogRecord;
import com.io7m.northpike.model.NPWorkItemStatus;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentExecution;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionSearchParameters;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCancelled;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreated;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreationFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateKind;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRequested;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRunning;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateSucceeded;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleHourlyHashed;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.assignments.NPAssignmentSearchParameters;
import com.io7m.northpike.model.comparisons.NPComparisonExactType;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanName;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.parsers.NPPlanSerializers;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.containers.NPDatabaseFixture;
import com.io7m.northpike.tests.containers.NPFixtures;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;

import java.io.IOException;
import java.net.URI;
import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionDeleteType.DeletionScope.DELETE_EVERYTHING;
import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabaseAssignmentsTest
{
  private static NPDatabaseFixture DATABASE_FIXTURE;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPDatabaseType database;
  private final NPStrings strings = NPStrings.create(Locale.ROOT);
  private NPRepositoryID repositoryId;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers)
    throws Exception
  {
    DATABASE_FIXTURE = NPFixtures.database(containers);
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

    this.repositoryId =
      new NPRepositoryID(randomUUID());

    this.transaction.setOwner(
      DATABASE_FIXTURE.userSetup(NPFixtures.idstore(containers).userWithLogin())
    );
  }

  /**
   * Creating assignments works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentCreate0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.PutType.class);

    final var planPut =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var reposPut =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class);
    final var scmPut =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A",
        URI.create("https://www.example.com")
      );
    scmPut.execute(scm);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("x.y"),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );
    reposPut.execute(repositoryDescription);

    final var plan =
      NPPlans.builder(NPStrings.create(Locale.ROOT), "x", 1L)
        .build();
    planPut.execute(
      new NPDatabaseQueriesPlansType.PutType.Parameters(
        plan, new NPPlanSerializers())
    );

    final var assignment =
      new NPAssignment(
        NPAssignmentName.of("x.y.z"),
        repositoryDescription.id(),
        plan.identifier(),
        new NPAssignmentScheduleHourlyHashed(OffsetDateTime.now().withNano(0))
      );

    put.execute(assignment);
    assertEquals(
      assignment,
      get.execute(assignment.name()).orElseThrow());
  }

  /**
   * Nonexistent assignments are nonexistent.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentGet0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.GetType.class);

    assertEquals(Optional.empty(), get.execute(NPAssignmentName.of("x.y")));
  }

  /**
   * Creating assignment executions works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentExecutionCreate0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.PutType.class);

    final var execGet =
      this.transaction.queries(
        ExecutionGetType.class);
    final var execPut =
      this.transaction.queries(
        ExecutionPutType.class);

    final var planPut =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var reposPut =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class);
    final var scmPut =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class);
    final var commitPut =
      this.transaction.queries(CommitsPutType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A",
        URI.create("https://www.example.com")
      );
    scmPut.execute(scm);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("x.y"),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );
    reposPut.execute(repositoryDescription);

    final var commit =
      new NPCommit(
        new NPCommitID(
          repositoryDescription.id(),
          new NPCommitUnqualifiedID("e5dc6e8b6dad3c58692b5b6a6ebbeaa30abe3cd9")
        ),
        OffsetDateTime.now().withNano(0),
        OffsetDateTime.now().withNano(0),
        new NPCommitAuthor("Author", "email"),
        "Subject",
        "Body",
        Set.of(),
        Set.of()
      );

    final var commitGraph =
      NPCommitGraph.create(Set.of());

    commitPut.execute(
      new CommitsPutType.Parameters(Set.of(commit), commitGraph));

    final var plan =
      NPPlans.builder(NPStrings.create(Locale.ROOT), "x", 1L)
        .build();
    planPut.execute(
      new NPDatabaseQueriesPlansType.PutType.Parameters(
        plan,
        new NPPlanSerializers())
    );

    final var assignment =
      new NPAssignment(
        NPAssignmentName.of("x.y.z"),
        repositoryDescription.id(),
        plan.identifier(),
        NPAssignmentScheduleNone.SCHEDULE_NONE
      );

    put.execute(assignment);

    final var executionId = new NPAssignmentExecutionID(randomUUID());

    NPAssignmentExecutionStateType execution =
      new NPAssignmentExecutionStateRequested(
        executionId,
        new NPAssignmentExecutionRequest(
          assignment.name(),
          commit.id().commitId()
        ),
        OffsetDateTime.now()
          .withNano(0)
      );

    execPut.execute(execution);

    execution = new NPAssignmentExecutionStateCreated(
      OffsetDateTime.now()
        .withNano(0),
      new NPAssignmentExecution(
        executionId,
        assignment,
        commit.id().commitId()
      )
    );

    execPut.execute(execution);

    assertEquals(
      execution,
      execGet.execute(execution.id()).orElseThrow()
    );

    execution = new NPAssignmentExecutionStateRunning(
      OffsetDateTime.now()
        .withNano(0),
      new NPAssignmentExecution(
        executionId,
        assignment,
        commit.id().commitId()
      ),
      OffsetDateTime.now()
        .withNano(0)
    );

    execPut.execute(execution);

    assertEquals(
      execution,
      execGet.execute(executionId).orElseThrow()
    );

    execution = new NPAssignmentExecutionStateSucceeded(
      OffsetDateTime.now()
        .withNano(0),
      new NPAssignmentExecution(
        executionId,
        assignment,
        commit.id().commitId()
      ),
      OffsetDateTime.now()
        .withNano(0),
      OffsetDateTime.now()
        .withNano(0)
    );

    execPut.execute(execution);

    assertEquals(
      execution,
      execGet.execute(executionId).orElseThrow()
    );

    execution = new NPAssignmentExecutionStateFailed(
      OffsetDateTime.now()
        .withNano(0),
      new NPAssignmentExecution(
        executionId,
        assignment,
        commit.id().commitId()
      ),
      OffsetDateTime.now()
        .withNano(0),
      OffsetDateTime.now()
        .withNano(0)
    );

    execPut.execute(execution);

    assertEquals(
      execution,
      execGet.execute(executionId).orElseThrow()
    );
  }

  /**
   * Nonexistent assignment executions are nonexistent.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentExecutionGet0()
    throws Exception
  {
    final var get =
      this.transaction.queries(ExecutionGetType.class);

    assertEquals(Optional.empty(), get.execute(new NPAssignmentExecutionID(
      randomUUID())));
  }

  /**
   * Creating work items works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testWorkItemCreate0()
    throws Exception
  {
    final var agentPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);

    final var put =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.PutType.class);

    final var execPut =
      this.transaction.queries(ExecutionPutType.class);

    final var planPut =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var reposPut =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class);
    final var scmPut =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class);
    final var commitPut =
      this.transaction.queries(CommitsPutType.class);

    final var workPut =
      this.transaction.queries(WorkItemPutType.class);
    final var workGet =
      this.transaction.queries(WorkItemGetType.class);
    final var workItemsGet =
      this.transaction.queries(ExecutionWorkItemsType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A",
        URI.create("https://www.example.com")
      );
    scmPut.execute(scm);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("x.y"),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );
    reposPut.execute(repositoryDescription);

    final var commit =
      new NPCommit(
        new NPCommitID(
          repositoryDescription.id(),
          new NPCommitUnqualifiedID("e5dc6e8b6dad3c58692b5b6a6ebbeaa30abe3cd9")
        ),
        OffsetDateTime.now().withNano(0),
        OffsetDateTime.now().withNano(0),
        new NPCommitAuthor("Author", "email"),
        "Subject",
        "Body",
        Set.of(),
        Set.of()
      );

    final var commitGraph =
      NPCommitGraph.create(Set.of());

    commitPut.execute(
      new CommitsPutType.Parameters(
        Set.of(commit),
        commitGraph
      ));

    final var plan =
      NPPlans.builder(NPStrings.create(Locale.ROOT), "x", 1L)
        .build();
    planPut.execute(
      new NPDatabaseQueriesPlansType.PutType.Parameters(
        plan,
        new NPPlanSerializers())
    );

    final var assignment =
      new NPAssignment(
        NPAssignmentName.of("x.y.z"),
        repositoryDescription.id(),
        plan.identifier(),
        NPAssignmentScheduleNone.SCHEDULE_NONE
      );

    put.execute(assignment);

    final var agent =
      new NPAgentDescription(
        new NPAgentID(randomUUID()),
        "Agent",
        new NPAgentKeyPairFactoryEd448().generateKeyPair().publicKey(),
        Map.of(),
        Map.of(),
        Map.of()
      );

    agentPut.execute(agent);

    final var execution =
      new NPAssignmentExecutionStateCreated(
        OffsetDateTime.now()
          .withNano(0),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignment,
          commit.id().commitId()
        )
      );

    execPut.execute(execution);

    final var identifier =
      new NPWorkItemIdentifier(
        execution.execution().id(),
        new RDottedName("some.task")
      );

    NPWorkItem workItem = null;
    for (final var state : NPWorkItemStatus.values()) {
      workItem = new NPWorkItem(identifier, Optional.of(agent.id()), state);

      workPut.execute(workItem);
      assertEquals(
        workItem,
        workGet.execute(identifier).orElseThrow()
      );
    }

    final var items =
      workItemsGet.execute(execution.id());

    assertEquals(Set.of(workItem), items);
  }

  /**
   * Searching assignments works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentSearch0()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var search =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.SearchType.class);

    final var paged =
      search.execute(new NPAssignmentSearchParameters(
        new NPComparisonExactType.Anything<>(),
        new NPComparisonExactType.Anything<>(),
        new NPComparisonFuzzyType.Anything<>(),
        1000L
      ));

    final var p = paged.pageCurrent(this.transaction);
    for (final var a : assignments) {
      assertTrue(p.items().contains(a));
    }
    assertEquals(9, p.items().size());
  }

  /**
   * Searching assignments works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentSearch1()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var search =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.SearchType.class);

    final var paged =
      search.execute(new NPAssignmentSearchParameters(
        new NPComparisonExactType.Anything<>(),
        new NPComparisonExactType.IsEqualTo<>(
          new NPPlanIdentifier(NPPlanName.of("orchid"), 1L)
        ),
        new NPComparisonFuzzyType.Anything<>(),
        1000L
      ));

    final var p = paged.pageCurrent(this.transaction);
    for (final var i : p.items()) {
      assertTrue(i.plan().name().name().value().contains("orchid"));
    }
    assertEquals(3, p.items().size());
  }

  /**
   * Searching assignments works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentSearch2()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var search =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.SearchType.class);

    final var paged =
      search.execute(new NPAssignmentSearchParameters(
        new NPComparisonExactType.IsEqualTo<>(this.repositoryId),
        new NPComparisonExactType.Anything<>(),
        new NPComparisonFuzzyType.Anything<>(),
        1000L
      ));

    final var p = paged.pageCurrent(this.transaction);
    for (final var a : assignments) {
      assertTrue(p.items().contains(a));
    }
    assertEquals(9, p.items().size());
  }

  /**
   * Searching assignments works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentSearch3()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var search =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.SearchType.class);

    final var paged =
      search.execute(new NPAssignmentSearchParameters(
        new NPComparisonExactType.IsEqualTo<>(this.repositoryId),
        new NPComparisonExactType.Anything<>(),
        new NPComparisonFuzzyType.IsSimilarTo<>("carrot"),
        1000L
      ));

    final var p = paged.pageCurrent(this.transaction);
    for (final var i : p.items()) {
      assertTrue(i.name().value().value().contains("carrot"));
    }
    assertEquals(3, p.items().size());
  }

  /**
   * Searching assignments works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentSearch4()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var search =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.SearchType.class);

    final var paged =
      search.execute(new NPAssignmentSearchParameters(
        new NPComparisonExactType.IsEqualTo<>(this.repositoryId),
        new NPComparisonExactType.Anything<>(),
        new NPComparisonFuzzyType.IsEqualTo<>("a.lavender.carrot"),
        1000L
      ));

    final var p = paged.pageCurrent(this.transaction);
    for (final var i : p.items()) {
      assertEquals("a.lavender.carrot", i.name().value().value());
    }
    assertEquals(1, p.items().size());
  }

  /**
   * Searching assignments works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentSearch5()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var search =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.SearchType.class);

    final var paged =
      search.execute(new NPAssignmentSearchParameters(
        new NPComparisonExactType.IsEqualTo<>(this.repositoryId),
        new NPComparisonExactType.Anything<>(),
        new NPComparisonFuzzyType.IsNotEqualTo<>("a.lavender.carrot"),
        1000L
      ));

    final var p = paged.pageCurrent(this.transaction);
    for (final var i : p.items()) {
      assertNotEquals("a.lavender.carrot", i.name().value().value());
    }
    assertEquals(8, p.items().size());
  }

  /**
   * Searching assignments works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentSearch6()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var search =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.SearchType.class);

    final var paged =
      search.execute(new NPAssignmentSearchParameters(
        new NPComparisonExactType.IsEqualTo<>(this.repositoryId),
        new NPComparisonExactType.Anything<>(),
        new NPComparisonFuzzyType.IsNotSimilarTo<>("carrot"),
        1000L
      ));

    final var p = paged.pageCurrent(this.transaction);
    for (final var i : p.items()) {
      assertFalse(i.name().value().value().contains("carrot"));
    }
    assertEquals(6, p.items().size());
  }

  /**
   * Searching assignments works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentSearch7()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var search =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.SearchType.class);

    final var paged =
      search.execute(new NPAssignmentSearchParameters(
        new NPComparisonExactType.IsEqualTo<>(this.repositoryId),
        new NPComparisonExactType.IsEqualTo<>(
          new NPPlanIdentifier(NPPlanName.of("rose"), 1L)
        ),
        new NPComparisonFuzzyType.Anything<>(),
        1000L
      ));

    final var p = paged.pageCurrent(this.transaction);
    for (final var i : p.items()) {
      assertEquals(
        new NPPlanIdentifier(NPPlanName.of("rose"), 1L),
        i.plan()
      );
    }
    assertEquals(3, p.items().size());
  }


  /**
   * Logging execution output works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentExecutionLog0()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var execution =
      new NPAssignmentExecutionStateCreated(
        OffsetDateTime.now()
          .withNano(0),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(0),
          new NPCommitUnqualifiedID("a")
        )
      );

    this.transaction.queries(ExecutionPutType.class)
      .execute(execution);

    this.transaction.queries(ExecutionLogAddType.class)
      .execute(new ExecutionLogAddType.Parameters(
        execution.id(),
        "INFO",
        "Some text.",
        Map.ofEntries(
          Map.entry("Key1", "Value1"),
          Map.entry("Key2", "Value2"),
          Map.entry("Key3", "Value3")
        ),
        Optional.of(NPStoredException.ofException(new IOException()))
      ));

    final var paged =
      this.transaction.queries(ExecutionLogListType.class)
        .execute(new ExecutionLogListType.Parameters(
          execution.id(),
          true,
          1000L
        ));

    final var page =
      paged.pageCurrent(this.transaction);

    assertEquals(1, page.pageIndex());
    assertEquals(1, page.pageCount());
    assertEquals(1, page.items().size());

    assertEquals(
      Map.ofEntries(
        Map.entry("Key1", "Value1"),
        Map.entry("Key2", "Value2"),
        Map.entry("Key3", "Value3")
      ),
      page.items().get(0).attributes()
    );
  }

  /**
   * Searching for executions works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentExecutionSearch0()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var executions =
      List.of(
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(0),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(1),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(2),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(3),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(4),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(5),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(6),
          new NPCommitUnqualifiedID("a")
        )
      );

    final var executionRecords =
      List.of(
        new NPAssignmentExecutionStateCancelled(
          executions.get(0).id(),
          executions.get(0).request(),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateCreated(
          OffsetDateTime.now().withNano(0),
          executions.get(1)
        ),
        new NPAssignmentExecutionStateCreationFailed(
          executions.get(2).id(),
          executions.get(2).request(),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateFailed(
          OffsetDateTime.now().withNano(0),
          executions.get(3),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateRequested(
          executions.get(4).id(),
          executions.get(4).request(),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateRunning(
          OffsetDateTime.now().withNano(0),
          executions.get(5),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateSucceeded(
          OffsetDateTime.now().withNano(0),
          executions.get(6),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        )
      );

    for (final var r : executionRecords) {
      this.transaction.queries(ExecutionPutType.class)
        .execute(r);
    }

    this.transaction.commit();

    final var paged =
      this.transaction.queries(ExecutionSearchType.class)
        .execute(new NPAssignmentExecutionSearchParameters(
          new NPComparisonExactType.Anything<>(),
          new NPComparisonExactType.Anything<>(),
          new NPComparisonExactType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          1000L
        ));

    final var page =
      paged.pageCurrent(this.transaction);

    assertEquals(1, page.pageIndex());
    assertEquals(1, page.pageCount());
    assertEquals(7, page.items().size());

    for (final var r : executionRecords) {
      assertTrue(
        page.items().contains(r),
        "List %s must contain %s".formatted(page.items(), r)
      );
    }
  }

  /**
   * Searching for executions works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentExecutionSearch1()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var executions =
      List.of(
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(0),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(1),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(2),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(3),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(4),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(5),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(6),
          new NPCommitUnqualifiedID("a")
        )
      );

    final var executionRecords =
      List.of(
        new NPAssignmentExecutionStateCancelled(
          executions.get(0).id(),
          executions.get(0).request(),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateCreated(
          OffsetDateTime.now().withNano(0),
          executions.get(1)
        ),
        new NPAssignmentExecutionStateCreationFailed(
          executions.get(2).id(),
          executions.get(2).request(),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateFailed(
          OffsetDateTime.now().withNano(0),
          executions.get(3),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateRequested(
          executions.get(4).id(),
          executions.get(4).request(),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateRunning(
          OffsetDateTime.now().withNano(0),
          executions.get(5),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateSucceeded(
          OffsetDateTime.now().withNano(0),
          executions.get(6),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        )
      );

    for (final var r : executionRecords) {
      this.transaction.queries(ExecutionPutType.class)
        .execute(r);
    }

    this.transaction.commit();

    for (final var status : NPAssignmentExecutionStateKind.values()) {
      final var paged =
        this.transaction.queries(ExecutionSearchType.class)
          .execute(new NPAssignmentExecutionSearchParameters(
            new NPComparisonExactType.Anything<>(),
            new NPComparisonExactType.Anything<>(),
            new NPComparisonExactType.IsEqualTo<>(status),
            new NPComparisonFuzzyType.Anything<>(),
            1000L
          ));

      final var page =
        paged.pageCurrent(this.transaction);

      assertEquals(1, page.pageIndex());
      assertEquals(1, page.pageCount());
      assertEquals(1, page.items().size());
    }
  }

  /**
   * Searching for executions works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentExecutionSearch2()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var executions =
      List.of(
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(0),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(1),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(2),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(3),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(4),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(5),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(6),
          new NPCommitUnqualifiedID("a")
        )
      );

    final var executionRecords =
      List.of(
        new NPAssignmentExecutionStateCancelled(
          executions.get(0).id(),
          executions.get(0).request(),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateCreated(
          OffsetDateTime.now().withNano(0),
          executions.get(1)
        ),
        new NPAssignmentExecutionStateCreationFailed(
          executions.get(2).id(),
          executions.get(2).request(),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateFailed(
          OffsetDateTime.now().withNano(0),
          executions.get(3),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateRequested(
          executions.get(4).id(),
          executions.get(4).request(),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateRunning(
          OffsetDateTime.now().withNano(0),
          executions.get(5),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateSucceeded(
          OffsetDateTime.now().withNano(0),
          executions.get(6),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        )
      );

    for (final var r : executionRecords) {
      this.transaction.queries(ExecutionPutType.class)
        .execute(r);
    }

    this.transaction.commit();

    for (final var status : NPAssignmentExecutionStateKind.values()) {
      final var paged =
        this.transaction.queries(ExecutionSearchType.class)
          .execute(new NPAssignmentExecutionSearchParameters(
            new NPComparisonExactType.Anything<>(),
            new NPComparisonExactType.Anything<>(),
            new NPComparisonExactType.IsNotEqualTo<>(status),
            new NPComparisonFuzzyType.Anything<>(),
            1000L
          ));

      final var page =
        paged.pageCurrent(this.transaction);

      assertEquals(1, page.pageIndex());
      assertEquals(1, page.pageCount());
      assertEquals(6, page.items().size());
    }
  }

  /**
   * Searching for executions works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentExecutionSearch3()
    throws Exception
  {
    final var assignments =
      this.createSampleAssignments();

    final var executions =
      List.of(
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(0),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(1),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(2),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(3),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(4),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(5),
          new NPCommitUnqualifiedID("a")
        ),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignments.get(6),
          new NPCommitUnqualifiedID("a")
        )
      );

    final var executionRecords =
      List.of(
        new NPAssignmentExecutionStateCancelled(
          executions.get(0).id(),
          executions.get(0).request(),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateCreated(
          OffsetDateTime.now().withNano(0),
          executions.get(1)
        ),
        new NPAssignmentExecutionStateCreationFailed(
          executions.get(2).id(),
          executions.get(2).request(),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateFailed(
          OffsetDateTime.now().withNano(0),
          executions.get(3),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateRequested(
          executions.get(4).id(),
          executions.get(4).request(),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateRunning(
          OffsetDateTime.now().withNano(0),
          executions.get(5),
          OffsetDateTime.now().withNano(0)
        ),
        new NPAssignmentExecutionStateSucceeded(
          OffsetDateTime.now().withNano(0),
          executions.get(6),
          OffsetDateTime.now().withNano(0),
          OffsetDateTime.now().withNano(0)
        )
      );

    for (final var r : executionRecords) {
      this.transaction.queries(ExecutionPutType.class)
        .execute(r);
    }

    this.transaction.commit();

    final var paged =
      this.transaction.queries(ExecutionSearchType.class)
        .execute(new NPAssignmentExecutionSearchParameters(
          new NPComparisonExactType.Anything<>(),
          new NPComparisonExactType.IsEqualTo<>(
            new NPPlanIdentifier(NPPlanName.of("rose"), 1L)
          ),
          new NPComparisonExactType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          1000L
        ));

    final var page =
      paged.pageCurrent(this.transaction);

    for (final var item : page.items()) {
      assertTrue(
        item.request().assignment().value().value().startsWith("a.rose.")
      );
    }

    assertEquals(1, page.pageIndex());
    assertEquals(1, page.pageCount());
    assertEquals(2, page.items().size());
  }

  private List<NPAssignment> createSampleAssignments()
    throws NPException
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.PutType.class);
    final var planPut =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var reposPut =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class);
    final var commitPut =
      this.transaction.queries(CommitsPutType.class);
    final var scmPut =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A",
        URI.create("https://www.example.com")
      );
    scmPut.execute(scm);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("x.y"),
        this.repositoryId,
        URI.create("https://www.example.com"),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );
    reposPut.execute(repositoryDescription);

    final var commit =
      new NPCommit(
        new NPCommitID(
          repositoryDescription.id(),
          new NPCommitUnqualifiedID("a")
        ),
        OffsetDateTime.now(),
        OffsetDateTime.now(),
        new NPCommitAuthor("Author", "x@example.com"),
        "Subject",
        "Body",
        Set.of(),
        Set.of()
      );

    commitPut.execute(
      new CommitsPutType.Parameters(
        Set.of(commit),
        NPCommitGraph.create(Set.of())
      )
    );

    final var plan0 =
      NPPlans.builder(this.strings, "rose", 1L)
        .build();
    final var plan1 =
      NPPlans.builder(this.strings, "lavender", 1L)
        .build();
    final var plan2 =
      NPPlans.builder(this.strings, "orchid", 1L)
        .build();

    planPut.execute(
      new NPDatabaseQueriesPlansType.PutType.Parameters(
        plan0, new NPPlanSerializers())
    );
    planPut.execute(
      new NPDatabaseQueriesPlansType.PutType.Parameters(
        plan1, new NPPlanSerializers())
    );
    planPut.execute(
      new NPDatabaseQueriesPlansType.PutType.Parameters(
        plan2, new NPPlanSerializers())
    );

    final var assignments = new ArrayList<NPAssignment>();
    for (final var p : List.of(plan0, plan1, plan2)) {
      for (int index = 0; index < 3; ++index) {
        final var assignmentName =
          NPAssignmentName.of(
            "a.%s.%s"
              .formatted(
                p.identifier().name(),
                switch (index) {
                  case 0 -> "corn";
                  case 1 -> "cabbage";
                  case 2 -> "carrot";
                  default -> throw new IllegalStateException();
                }
              )
          );

        final var assignment =
          new NPAssignment(
            assignmentName,
            repositoryDescription.id(),
            p.identifier(),
            NPAssignmentScheduleNone.SCHEDULE_NONE
          );

        assignments.add(assignment);
        put.execute(assignment);
      }
    }

    this.transaction.commit();
    return List.copyOf(assignments);
  }

  /**
   * Deleting assignment executions works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentExecutionDelete0()
    throws Exception
  {
    final var agentPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.PutType.class);
    final var execGet =
      this.transaction.queries(ExecutionGetType.class);
    final var execPut =
      this.transaction.queries(ExecutionPutType.class);
    final var execLogAdd =
      this.transaction.queries(ExecutionLogAddType.class);
    final var execDelete =
      this.transaction.queries(ExecutionDeleteType.class);
    final var planPut =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var reposPut =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class);
    final var scmPut =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class);
    final var commitPut =
      this.transaction.queries(CommitsPutType.class);
    final var workPut =
      this.transaction.queries(WorkItemPutType.class);
    final var workLogAdd =
      this.transaction.queries(WorkItemLogAddType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A",
        URI.create("https://www.example.com")
      );
    scmPut.execute(scm);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("x.y"),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );
    reposPut.execute(repositoryDescription);

    final var commit =
      new NPCommit(
        new NPCommitID(
          repositoryDescription.id(),
          new NPCommitUnqualifiedID("e5dc6e8b6dad3c58692b5b6a6ebbeaa30abe3cd9")
        ),
        OffsetDateTime.now().withNano(0),
        OffsetDateTime.now().withNano(0),
        new NPCommitAuthor("Author", "email"),
        "Subject",
        "Body",
        Set.of(),
        Set.of()
      );

    final var commitGraph =
      NPCommitGraph.create(Set.of());

    commitPut.execute(
      new CommitsPutType.Parameters(
        Set.of(commit),
        commitGraph
      ));

    final var plan =
      NPPlans.builder(NPStrings.create(Locale.ROOT), "x", 1L)
        .build();
    planPut.execute(
      new NPDatabaseQueriesPlansType.PutType.Parameters(
        plan,
        new NPPlanSerializers())
    );

    final var assignment =
      new NPAssignment(
        NPAssignmentName.of("x.y.z"),
        repositoryDescription.id(),
        plan.identifier(),
        NPAssignmentScheduleNone.SCHEDULE_NONE
      );

    put.execute(assignment);

    final var agent =
      new NPAgentDescription(
        new NPAgentID(randomUUID()),
        "Agent",
        new NPAgentKeyPairFactoryEd448().generateKeyPair().publicKey(),
        Map.of(),
        Map.of(),
        Map.of()
      );

    agentPut.execute(agent);

    final var execution =
      new NPAssignmentExecutionStateCreated(
        OffsetDateTime.now()
          .withNano(0),
        new NPAssignmentExecution(
          new NPAssignmentExecutionID(randomUUID()),
          assignment,
          commit.id().commitId()
        )
      );

    execPut.execute(execution);

    final var identifier =
      new NPWorkItemIdentifier(
        execution.execution().id(),
        new RDottedName("some.task")
      );

    NPWorkItem workItem;
    for (final var state : NPWorkItemStatus.values()) {
      workItem = new NPWorkItem(identifier, Optional.of(agent.id()), state);
      workPut.execute(workItem);

      for (int index = 0; index < 10; ++index) {
        workLogAdd.execute(new NPWorkItemLogRecord(
          workItem.identifier(),
          OffsetDateTime.now(),
          Map.of("a", "x", "b", "y"),
          "Line %d".formatted(Integer.valueOf(index)),
          Optional.of(NPStoredException.ofException(new IOException()))
        ));
      }
    }

    for (int index = 0; index < 100; ++index) {
      execLogAdd.execute(new ExecutionLogAddType.Parameters(
        execution.id(),
        "TEST",
        "Line " + index,
        Map.ofEntries(
          Map.entry("A", "X"),
          Map.entry("B", "Y"),
          Map.entry("C", "Z")
        ),
        Optional.of(NPStoredException.ofException(new IOException()))
      ));
    }

    execDelete.execute(new Parameters(execution.id(), DELETE_EVERYTHING));
    assertEquals(Optional.empty(), execGet.execute(execution.id()));
  }
}
