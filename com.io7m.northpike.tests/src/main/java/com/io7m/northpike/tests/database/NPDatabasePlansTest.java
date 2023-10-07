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

import com.io7m.anethum.api.ParsingException;
import com.io7m.anethum.api.SerializationException;
import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.ervilla.test_extension.ErvillaCloseAfterSuite;
import com.io7m.ervilla.test_extension.ErvillaConfiguration;
import com.io7m.ervilla.test_extension.ErvillaExtension;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.PutType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.PutExecutionDescriptionType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPRepositorySigningPolicy;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanSearchParameters;
import com.io7m.northpike.model.plans.NPPlanToolExecution;
import com.io7m.northpike.model.plans.NPPlanType;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanParserType;
import com.io7m.northpike.plans.parsers.NPPlanParsers;
import com.io7m.northpike.plans.parsers.NPPlanSerializerFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanSerializerType;
import com.io7m.northpike.plans.parsers.NPPlanSerializers;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.containers.NPTestContainerInstances;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.northpike.toolexec.NPTXFormats;
import com.io7m.verona.core.Version;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mockito;

import java.net.URI;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorPlanStillReferenced;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabasePlansTest
{
  private static NPTestContainers.NPDatabaseFixture DATABASE_FIXTURE;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPDatabaseType database;
  private NPPlanSerializerFactoryType failingSerializers;
  private NPPlanSerializerType failingSerializer;
  private NPPlanParserFactoryType failingParsers;
  private NPPlanParserType failingParser;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers)
    throws Exception
  {
    DATABASE_FIXTURE = NPTestContainerInstances.database(containers);
  }

  private static List<NPPlanType> createPlans(
    final NPDatabaseQueriesPlansType.PutType put)
    throws NPPlanException, NPDatabaseException
  {
    final var strings =
      NPStrings.create(Locale.ROOT);

    final var plan0 =
      NPPlans.builder(strings, "com.io7m.p", 1L)
        .setDescription("Abacus")
        .build();
    final var plan1 =
      NPPlans.builder(strings, "com.io7m.q", 2L)
        .setDescription("Marimba")
        .build();
    final var plan2 =
      NPPlans.builder(strings, "com.io7m.r", 3L)
        .setDescription("Nova")
        .build();

    put.execute(new Parameters(plan0, new NPPlanSerializers()));
    put.execute(new Parameters(plan1, new NPPlanSerializers()));
    put.execute(new Parameters(plan2, new NPPlanSerializers()));

    return List.of(plan0, plan1, plan2);
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

    this.failingSerializers =
      Mockito.mock(NPPlanSerializerFactoryType.class);
    this.failingSerializer =
      Mockito.mock(NPPlanSerializerType.class);

    Mockito.when(this.failingSerializers.createSerializer(any(), any()))
      .thenReturn(this.failingSerializer);

    Mockito.doThrow(
        new SerializationException("Ouch!")
      ).when(this.failingSerializer)
      .execute(any());

    this.failingParsers =
      Mockito.mock(NPPlanParserFactoryType.class);
    this.failingParser =
      Mockito.mock(NPPlanParserType.class);

    Mockito.doThrow(
        new ParsingException("Ouch!", List.of())
      ).when(this.failingParsers)
      .parse(any(), any());

    this.transaction.setOwner(
      NPTestContainers.NPDatabaseFixture.createUser(
        this.transaction,
        UUID.randomUUID()
      )
    );
  }

  /**
   * Creating plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanCreate0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetType.class);
    final var getRaw =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetUnparsedType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final var plan =
      NPPlans.builder(strings, "com.io7m.p", 1L)
        .build();

    put.execute(
      new Parameters(
        plan,
        new NPPlanSerializers())
    );

    final var planAfter =
      NPPlans.toPlan(
        get.execute(
          new NPDatabaseQueriesPlansType.GetType.Parameters(
            plan.identifier(),
            Set.of(new NPPlanParsers()))
        ).orElseThrow(),
        strings
      );

    assertEquals(plan.identifier(), planAfter.identifier());
    assertEquals(plan.elements(), planAfter.elements());
    assertEquals(plan.toolReferences(), planAfter.toolReferences());

    getRaw.execute(plan.identifier())
      .orElseThrow();
  }

  /**
   * Creating plans fails if serialization fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanCreateFail0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetType.class);
    final var getRaw =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetUnparsedType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final var plan =
      NPPlans.builder(strings, "com.io7m.p", 1L)
        .build();

    final var ex =
      assertThrows(NPDatabaseException.class, () -> {
        put.execute(
          new Parameters(
            plan,
            this.failingSerializers
          )
        );
      });

    assertInstanceOf(SerializationException.class, ex.getCause());

    assertEquals(Optional.empty(), getRaw.execute(plan.identifier()));
  }

  /**
   * Getting plans fails if parsing fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanGetFail0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetType.class);
    final var getRaw =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetUnparsedType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final var plan =
      NPPlans.builder(strings, "com.io7m.p", 1L)
        .build();

    final var serializers = new NPPlanSerializers();
    put.execute(
      new Parameters(plan, serializers)
    );

    Mockito.when(this.failingParsers.formats())
      .thenReturn(serializers.formats());

    final var ex =
      assertThrows(NPDatabaseException.class, () -> {
        get.execute(
          new NPDatabaseQueriesPlansType.GetType.Parameters(
            plan.identifier(),
            Set.of(this.failingParsers))
        );
      });

    assertInstanceOf(ParsingException.class, ex.getCause());

    getRaw.execute(plan.identifier())
      .orElseThrow();
  }

  /**
   * Getting plans fails if there are no supported formats.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanGetFail1()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetType.class);
    final var getRaw =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetUnparsedType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final var plan =
      NPPlans.builder(strings, "com.io7m.p", 1L)
        .build();

    final var serializers = new NPPlanSerializers();
    put.execute(
      new Parameters(plan, serializers)
    );

    Mockito.when(this.failingParsers.formats())
      .thenReturn(Set.of());

    final var ex =
      assertThrows(NPDatabaseException.class, () -> {
        get.execute(
          new NPDatabaseQueriesPlansType.GetType.Parameters(
            plan.identifier(),
            Set.of(this.failingParsers))
        );
      });

    getRaw.execute(plan.identifier())
      .orElseThrow();
  }

  /**
   * Nonexistent plans are nonexistent.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanGet0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetType.class);
    final var getRaw =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetUnparsedType.class);

    assertEquals(
      Optional.empty(),
      get.execute(
        new NPDatabaseQueriesPlansType.GetType.Parameters(
          NPPlanIdentifier.of("x", 23L),
          Set.of(new NPPlanParsers())
        )
      )
    );

    assertEquals(
      Optional.empty(),
      getRaw.execute(
        NPPlanIdentifier.of("x", 23L)
      )
    );
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch0D()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var plans =
      createPlans(put);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.Anything<>(),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(0).identifier(), p.items().get(0).identifier());
    assertEquals(plans.get(1).identifier(), p.items().get(1).identifier());
    assertEquals(plans.get(2).identifier(), p.items().get(2).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch1D()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var plans =
      createPlans(put);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.IsSimilarTo<>("marimba"),
          new NPComparisonSetType.Anything<>(),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(1).identifier(), p.items().get(0).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch2D()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var plans =
      createPlans(put);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.IsNotSimilarTo<>("marimba"),
          new NPComparisonSetType.Anything<>(),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(0).identifier(), p.items().get(0).identifier());
    assertEquals(plans.get(2).identifier(), p.items().get(1).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch3D()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var plans =
      createPlans(put);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.IsEqualTo<>("Marimba"),
          new NPComparisonSetType.Anything<>(),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(1).identifier(), p.items().get(0).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch4D()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var plans =
      createPlans(put);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.IsNotEqualTo<>("Marimba"),
          new NPComparisonSetType.Anything<>(),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(0).identifier(), p.items().get(0).identifier());
    assertEquals(plans.get(2).identifier(), p.items().get(1).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch0N()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var plans =
      createPlans(put);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.Anything<>(),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(0).identifier(), p.items().get(0).identifier());
    assertEquals(plans.get(1).identifier(), p.items().get(1).identifier());
    assertEquals(plans.get(2).identifier(), p.items().get(2).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch1N()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var plans =
      createPlans(put);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.IsSimilarTo<>("p"),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.Anything<>(),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(0).identifier(), p.items().get(0).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch2N()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var plans =
      createPlans(put);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.IsNotSimilarTo<>("io7m"),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.Anything<>(),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(0, p.items().size());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch3N()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var plans =
      createPlans(put);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.IsEqualTo<>("com.io7m.r"),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.Anything<>(),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(2).identifier(), p.items().get(0).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch4N()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var plans =
      createPlans(put);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.IsNotEqualTo<>("com.io7m.q"),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.Anything<>(),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(0).identifier(), p.items().get(0).identifier());
    assertEquals(plans.get(2).identifier(), p.items().get(1).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Unreferenced plans can be deleted.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanDeleteIntegrity0()
    throws Exception
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var delete =
      this.transaction.queries(NPDatabaseQueriesPlansType.DeleteType.class);
    final var get =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetUnparsedType.class);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final var plan =
      NPPlans.builder(strings, "com.io7m.p", 1L)
        .build();

    put.execute(new Parameters(plan, new NPPlanSerializers()));

    assertNotEquals(
      Optional.empty(),
      get.execute(plan.identifier())
    );

    delete.execute(plan.identifier());

    assertEquals(
      Optional.empty(),
      get.execute(plan.identifier())
    );
  }

  /**
   * Referenced plans give a usable error message on deletion attempts.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanDeleteIntegrity1()
    throws Exception
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var delete =
      this.transaction.queries(NPDatabaseQueriesPlansType.DeleteType.class);
    final var get =
      this.transaction.queries(NPDatabaseQueriesPlansType.GetUnparsedType.class);
    final var assignPut =
      this.transaction.queries(NPDatabaseQueriesAssignmentsType.PutType.class);
    final var reposPut =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final var plan =
      NPPlans.builder(strings, "com.io7m.p", 1L)
        .build();

    put.execute(new Parameters(plan, new NPPlanSerializers()));

    final var repositoryID =
      new NPRepositoryID(UUID.randomUUID());

    reposPut.execute(new NPRepositoryDescription(
      NPSCMRepositoriesJGit.providerNameGet(),
      repositoryID,
      URI.create("http://www.example.com"),
      NPRepositoryCredentialsNone.CREDENTIALS_NONE,
      NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS
    ));

    assignPut.execute(new NPAssignment(
      NPAssignmentName.of("x"),
      repositoryID,
      plan.identifier(),
      NPAssignmentScheduleNone.SCHEDULE_NONE
    ));

    final var ex =
      assertThrows(NPDatabaseException.class, () -> {
        delete.execute(plan.identifier());
      });

    assertEquals(errorPlanStillReferenced(), ex.errorCode());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearchToolsSet0()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var toolPut =
      this.transaction.queries(PutExecutionDescriptionType.class);

    final var plans =
      createPlansWithMultipleTools(put, toolPut);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.IsEqualTo<>(
            Set.of(
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                23L
              ),
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                24L
              ),
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                25L
              )
            )
          ),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(0).identifier(), p.items().get(0).identifier());
    assertEquals(1, p.items().size());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearchToolsSet1()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var toolPut =
      this.transaction.queries(PutExecutionDescriptionType.class);

    final var plans =
      createPlansWithMultipleTools(put, toolPut);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.IsSupersetOf<>(
            Set.of(
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                23L
              ),
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                24L
              ),
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                25L
              )
            )
          ),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(0).identifier(), p.items().get(0).identifier());
    assertEquals(1, p.items().size());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearchToolsSet2()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var toolPut =
      this.transaction.queries(PutExecutionDescriptionType.class);

    final var plans =
      createPlansWithMultipleTools(put, toolPut);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.IsSubsetOf<>(
            Set.of(
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                23L
              ),
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                24L
              ),
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                25L
              )
            )
          ),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(0).identifier(), p.items().get(0).identifier());
    assertEquals(plans.get(1).identifier(), p.items().get(1).identifier());
    assertEquals(plans.get(2).identifier(), p.items().get(2).identifier());
    assertEquals(3, p.items().size());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearchToolsSet3()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var toolPut =
      this.transaction.queries(PutExecutionDescriptionType.class);

    final var plans =
      createPlansWithMultipleTools(put, toolPut);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.IsNotEqualTo<>(
            Set.of(
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                23L
              ),
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                24L
              ),
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                25L
              )
            )
          ),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(1).identifier(), p.items().get(0).identifier());
    assertEquals(plans.get(2).identifier(), p.items().get(1).identifier());
    assertEquals(2, p.items().size());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Searching for plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearchToolsSet4()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);
    final var toolPut =
      this.transaction.queries(PutExecutionDescriptionType.class);

    final var plans =
      createPlansWithMultipleTools(put, toolPut);

    this.transaction.commit();

    final var r =
      search.execute(
        new NPPlanSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonSetType.IsOverlapping<>(
            Set.of(
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of("com.io7m.example"),
                24L
              )
            )
          ),
          1000L
        )
      );

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plans.get(0).identifier(), p.items().get(0).identifier());
    assertEquals(plans.get(1).identifier(), p.items().get(1).identifier());
    assertEquals(2, p.items().size());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  private static List<NPPlanType> createPlansWithMultipleTools(
    final NPDatabaseQueriesPlansType.PutType put,
    final PutExecutionDescriptionType toolPut)
    throws NPDatabaseException, NPPlanException
  {
    final var tool0 =
      new NPToolExecutionDescription(
        new NPToolExecutionIdentifier(
          NPToolExecutionName.of("com.io7m.example"),
          23L
        ),
        NPToolName.of("com.io7m.tool"),
        "A description.",
        NPTXFormats.nptx1(),
        "Data."
      );

    final var tool1 =
      new NPToolExecutionDescription(
        new NPToolExecutionIdentifier(
          NPToolExecutionName.of("com.io7m.example"),
          24L
        ),
        NPToolName.of("com.io7m.tool"),
        "A description.",
        NPTXFormats.nptx1(),
        "Data."
      );

    final var tool2 =
      new NPToolExecutionDescription(
        new NPToolExecutionIdentifier(
          NPToolExecutionName.of("com.io7m.example"),
          25L
        ),
        NPToolName.of("com.io7m.tool"),
        "A description.",
        NPTXFormats.nptx1(),
        "Data."
      );

    toolPut.execute(tool0);
    toolPut.execute(tool1);
    toolPut.execute(tool2);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final var plans =
      new ArrayList<NPPlanType>();

    {
      final var planBuilder =
        NPPlans.builder(strings, "com.io7m.p0", 1L);

      planBuilder.addToolReference(
        new NPToolReference(
          NPToolReferenceName.of("t0"),
          NPToolName.of("t1"),
          Version.of(1, 0, 0)
        )
      );

      planBuilder.addTask("e")
        .setToolExecution(
          new NPPlanToolExecution(
            NPToolReferenceName.of("t0"),
            tool0.identifier(),
            Set.of()
          )
        );

      planBuilder.addTask("f")
        .setToolExecution(
          new NPPlanToolExecution(
            NPToolReferenceName.of("t0"),
            tool1.identifier(),
            Set.of()
          )
        );

      planBuilder.addTask("g")
        .setToolExecution(
          new NPPlanToolExecution(
            NPToolReferenceName.of("t0"),
            tool2.identifier(),
            Set.of()
          )
        );

      final var plan = planBuilder.build();
      put.execute(new Parameters(plan, new NPPlanSerializers()));
      plans.add(plan);
    }

    {
      final var planBuilder =
        NPPlans.builder(strings, "com.io7m.p1", 1L);

      planBuilder.addToolReference(
        new NPToolReference(
          NPToolReferenceName.of("t0"),
          NPToolName.of("t1"),
          Version.of(1, 0, 0)
        )
      );

      planBuilder.addTask("e")
        .setToolExecution(
          new NPPlanToolExecution(
            NPToolReferenceName.of("t0"),
            tool0.identifier(),
            Set.of()
          )
        );

      planBuilder.addTask("f")
        .setToolExecution(
          new NPPlanToolExecution(
            NPToolReferenceName.of("t0"),
            tool1.identifier(),
            Set.of()
          )
        );

      final var plan = planBuilder.build();
      put.execute(new Parameters(plan, new NPPlanSerializers()));
      plans.add(plan);
    }

    {
      final var planBuilder =
        NPPlans.builder(strings, "com.io7m.p2", 1L);

      planBuilder.addToolReference(
        new NPToolReference(
          NPToolReferenceName.of("t0"),
          NPToolName.of("t1"),
          Version.of(1, 0, 0)
        )
      );

      planBuilder.addTask("e")
        .setToolExecution(
          new NPPlanToolExecution(
            NPToolReferenceName.of("t0"),
            tool0.identifier(),
            Set.of()
          )
        );

      final var plan = planBuilder.build();
      put.execute(new Parameters(plan, new NPPlanSerializers()));
      plans.add(plan);
    }

    return plans;
  }
}
