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
import com.io7m.ervilla.test_extension.ErvillaCloseAfterAll;
import com.io7m.ervilla.test_extension.ErvillaConfiguration;
import com.io7m.ervilla.test_extension.ErvillaExtension;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.assignments.NPAssignment;
import com.io7m.northpike.assignments.NPAssignmentExecution;
import com.io7m.northpike.assignments.NPAssignmentExecutionCreated;
import com.io7m.northpike.assignments.NPAssignmentExecutionFailed;
import com.io7m.northpike.assignments.NPAssignmentExecutionRunning;
import com.io7m.northpike.assignments.NPAssignmentExecutionSucceeded;
import com.io7m.northpike.assignments.NPAssignmentName;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesSCMProvidersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitGraph;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.parsers.NPPlanSerializers;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;

import java.net.URI;
import java.time.OffsetDateTime;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static org.junit.jupiter.api.Assertions.assertEquals;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(disabledIfUnsupported = true)
public final class NPDatabaseAssignmentsTest
{
  private static NPTestContainers.NPDatabaseFixture DATABASE_FIXTURE;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPDatabaseType database;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterAll EContainerSupervisorType containers)
    throws Exception
  {
    DATABASE_FIXTURE =
      NPTestContainers.createDatabase(containers, 15432);
  }

  @BeforeEach
  public void setup(
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
        UUID.randomUUID(),
        URI.create("https://www.example.com"),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE
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
        plan.identifier()
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
        NPDatabaseQueriesAssignmentsType.ExecutionGetType.class);
    final var execPut =
      this.transaction.queries(
        NPDatabaseQueriesAssignmentsType.ExecutionPutType.class);

    final var planPut =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var reposPut =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class);
    final var scmPut =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class);
    final var commitPut =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.CommitsPutType.class);

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
        UUID.randomUUID(),
        URI.create("https://www.example.com"),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE
      );
    reposPut.execute(repositoryDescription);

    final var commit =
      new NPCommit(
        new NPCommitID(
          repositoryDescription.id(),
          "e5dc6e8b6dad3c58692b5b6a6ebbeaa30abe3cd9"
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
      new NPDatabaseQueriesRepositoriesType.CommitsPutType.Parameters(
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
        plan.identifier()
      );

    put.execute(assignment);

    var execution =
      new NPAssignmentExecution(
        UUID.randomUUID(),
        assignment,
        commit.id(),
        new NPAssignmentExecutionCreated(
          OffsetDateTime.now()
            .withNano(0)
        )
      );

    execPut.execute(execution);

    assertEquals(
      execution,
      execGet.execute(execution.executionId()).orElseThrow()
    );

    execution = execution.withStatus(
      new NPAssignmentExecutionRunning(
        OffsetDateTime.now()
          .withNano(0),
        OffsetDateTime.now()
          .withNano(0)
      )
    );

    execPut.execute(execution);

    assertEquals(
      execution,
      execGet.execute(execution.executionId()).orElseThrow()
    );

    execution = execution.withStatus(
      new NPAssignmentExecutionSucceeded(
        OffsetDateTime.now()
          .withNano(0),
        OffsetDateTime.now()
          .withNano(0),
        OffsetDateTime.now()
          .withNano(0)
      )
    );

    execPut.execute(execution);

    assertEquals(
      execution,
      execGet.execute(execution.executionId()).orElseThrow()
    );

    execution = execution.withStatus(
      new NPAssignmentExecutionFailed(
        OffsetDateTime.now()
          .withNano(0),
        OffsetDateTime.now()
          .withNano(0),
        OffsetDateTime.now()
          .withNano(0)
      )
    );

    execPut.execute(execution);

    assertEquals(
      execution,
      execGet.execute(execution.executionId()).orElseThrow()
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
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.ExecutionGetType.class);

    assertEquals(Optional.empty(), get.execute(UUID.randomUUID()));
  }
}
