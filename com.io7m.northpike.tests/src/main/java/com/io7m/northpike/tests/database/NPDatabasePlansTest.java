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
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.PutType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.plans.NPPlanIdentifier;
import com.io7m.northpike.plans.NPPlanSearchParameters;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanParserType;
import com.io7m.northpike.plans.parsers.NPPlanParsers;
import com.io7m.northpike.plans.parsers.NPPlanSerializerFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanSerializerType;
import com.io7m.northpike.plans.parsers.NPPlanSerializers;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.containers.NPTestContainerInstances;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mockito;

import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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
      get.execute(
          new NPDatabaseQueriesPlansType.GetType.Parameters(
            plan.identifier(),
            Set.of(new NPPlanParsers()))
        ).orElseThrow()
        .toPlan(strings);

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
   * Creating plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch0()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final var plan0 =
      NPPlans.builder(strings, "com.io7m.p", 1L)
        .build();
    final var plan1 =
      NPPlans.builder(strings, "com.io7m.p", 2L)
        .build();
    final var plan2 =
      NPPlans.builder(strings, "com.io7m.p", 3L)
        .build();

    put.execute(new Parameters(plan0, new NPPlanSerializers()));
    put.execute(new Parameters(plan1, new NPPlanSerializers()));
    put.execute(new Parameters(plan2, new NPPlanSerializers()));

    this.transaction.commit();

    final var r =
      search.execute(new NPPlanSearchParameters("", 1000L));

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plan0.identifier(), p.items().get(0).identifier());
    assertEquals(plan1.identifier(), p.items().get(1).identifier());
    assertEquals(plan2.identifier(), p.items().get(2).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }

  /**
   * Creating plans works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanSearch1()
    throws Exception
  {
    final var search =
      this.transaction.queries(NPDatabaseQueriesPlansType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final var plan0 =
      NPPlans.builder(strings, "com.io7m.p", 1L)
        .setDescription("Abacus")
        .build();
    final var plan1 =
      NPPlans.builder(strings, "com.io7m.p", 2L)
        .setDescription("Marimba")
        .build();
    final var plan2 =
      NPPlans.builder(strings, "com.io7m.p", 3L)
        .setDescription("Nova")
        .build();

    put.execute(new Parameters(plan0, new NPPlanSerializers()));
    put.execute(new Parameters(plan1, new NPPlanSerializers()));
    put.execute(new Parameters(plan2, new NPPlanSerializers()));

    this.transaction.commit();

    final var r =
      search.execute(new NPPlanSearchParameters("marimba", 1000L));

    final var p =
      r.pageCurrent(this.transaction);

    assertEquals(plan1.identifier(), p.items().get(0).identifier());
    assertEquals(1, p.pageCount());
    assertEquals(1, p.pageIndex());
    assertEquals(0L, p.pageFirstOffset());
  }
}
