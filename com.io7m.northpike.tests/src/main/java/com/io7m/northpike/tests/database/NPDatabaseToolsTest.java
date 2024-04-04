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
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.PlanPutType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.DeleteExecutionDescriptionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.GetExecutionDescriptionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.PutExecutionDescriptionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.SearchExecutionDescriptionType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionDescriptionSearchParameters;
import com.io7m.northpike.model.NPToolExecutionDescriptionSummary;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.comparisons.NPComparisonExactType;
import com.io7m.northpike.model.plans.NPPlanToolExecution;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.parsers.NPPlanSerializers;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.containers.NPDatabaseFixture;
import com.io7m.northpike.tests.containers.NPFixtures;
import com.io7m.verona.core.Version;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;

import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorToolExecutionStillReferenced;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabaseToolsTest
{
  private static NPDatabaseFixture DATABASE_FIXTURE;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPDatabaseType database;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers)
    throws Exception
  {
    DATABASE_FIXTURE = NPFixtures.database(NPFixtures.pod(containers));
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

    this.transaction.setOwner(
      DATABASE_FIXTURE.userSetup(
        NPFixtures.idstore(NPFixtures.pod(containers)).userWithLogin())
    );
  }

  /**
   * Creating tool execution descriptions works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecCreate0()
    throws Exception
  {
    final var get =
      this.transaction.queries(GetExecutionDescriptionType.class);
    final var put =
      this.transaction.queries(PutExecutionDescriptionType.class);

    final var tool =
      new NPToolExecutionDescription(
        new NPToolExecutionIdentifier(
          NPToolExecutionName.of("com.io7m.example"),
          23L
        ),
        NPToolName.of("com.io7m.tool"),
        "A description.",
        NPFormatName.of("com.io7m.northpike.toolexec.js"),
        "execution.argumentAdd('ok')"
      );

    put.execute(tool);
    assertEquals(tool, get.execute(tool.identifier()).orElseThrow());
  }

  /**
   * Nonexistent tool execution descriptions are nonexistent.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecGet0()
    throws Exception
  {
    final var get =
      this.transaction.queries(GetExecutionDescriptionType.class);

    assertEquals(
      Optional.empty(),
      get.execute(new NPToolExecutionIdentifier(
        NPToolExecutionName.of("com.io7m.example"),
        23L
      ))
    );
  }

  /**
   * Searching for tool execution descriptions works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecSearch0()
    throws Exception
  {
    final var put =
      this.transaction.queries(PutExecutionDescriptionType.class);
    final var search =
      this.transaction.queries(SearchExecutionDescriptionType.class);

    for (int toolIndex = 0; toolIndex < 3; ++toolIndex) {
      for (long version = 1L; version <= 3L; ++version) {
        final var tool =
          new NPToolExecutionDescription(
            new NPToolExecutionIdentifier(
              NPToolExecutionName.of(
                "com.io7m.example_%d"
                  .formatted(Integer.valueOf(toolIndex))
              ),
              version
            ),
            NPToolName.of("com.io7m.tool_%d"
                            .formatted(Integer.valueOf(toolIndex))),
            "A description.",
            NPFormatName.of("com.io7m.northpike.toolexec.js"),
            "execution.argumentAdd('ok')"
          );
        put.execute(tool);
      }
    }

    final var paged =
      search.execute(new NPToolExecutionDescriptionSearchParameters(
        new NPComparisonExactType.IsEqualTo<>(
          NPToolName.of("com.io7m.tool_2")
        ),
        1000L)
      );

    final var p = paged.pageCurrent(this.transaction);
    assertEquals(1, p.pageIndex());
    assertEquals(1, p.pageCount());
    assertEquals(0L, p.pageFirstOffset());
    assertEquals(
      List.of(
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_2"),
            1L
          ),
          NPToolName.of("com.io7m.tool_2"),
          "A description."
        ),
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_2"),
            2L
          ),
          NPToolName.of("com.io7m.tool_2"),
          "A description."
        ),
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_2"),
            3L
          ),
          NPToolName.of("com.io7m.tool_2"),
          "A description."
        )
      ),
      p.items()
    );
  }

  /**
   * Searching for tool execution descriptions works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecSearch1()
    throws Exception
  {
    final var put =
      this.transaction.queries(PutExecutionDescriptionType.class);
    final var search =
      this.transaction.queries(SearchExecutionDescriptionType.class);

    for (int toolIndex = 0; toolIndex < 3; ++toolIndex) {
      for (long version = 1L; version <= 3L; ++version) {
        final var tool =
          new NPToolExecutionDescription(
            new NPToolExecutionIdentifier(
              NPToolExecutionName.of(
                "com.io7m.example_%d"
                  .formatted(Integer.valueOf(toolIndex))
              ),
              version
            ),
            NPToolName.of("com.io7m.tool_%d"
                            .formatted(Integer.valueOf(toolIndex))),
            "A description.",
            NPFormatName.of("com.io7m.northpike.toolexec.js"),
            "execution.argumentAdd('ok')"
          );
        put.execute(tool);
      }
    }

    this.transaction.commit();

    final var paged =
      search.execute(new NPToolExecutionDescriptionSearchParameters(
        new NPComparisonExactType.Anything<>(), 1000L)
      );

    final var p = paged.pageCurrent(this.transaction);
    assertEquals(1, p.pageIndex());
    assertEquals(1, p.pageCount());
    assertEquals(0L, p.pageFirstOffset());
    assertEquals(
      List.of(
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_0"),
            1L
          ),
          NPToolName.of("com.io7m.tool_0"),
          "A description."
        ),
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_0"),
            2L
          ),
          NPToolName.of("com.io7m.tool_0"),
          "A description."
        ),
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_0"),
            3L
          ),
          NPToolName.of("com.io7m.tool_0"),
          "A description."
        ),
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_1"),
            1L
          ),
          NPToolName.of("com.io7m.tool_1"),
          "A description."
        ),
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_1"),
            2L
          ),
          NPToolName.of("com.io7m.tool_1"),
          "A description."
        ),
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_1"),
            3L
          ),
          NPToolName.of("com.io7m.tool_1"),
          "A description."
        ),
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_2"),
            1L
          ),
          NPToolName.of("com.io7m.tool_2"),
          "A description."
        ),
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_2"),
            2L
          ),
          NPToolName.of("com.io7m.tool_2"),
          "A description."
        ),
        new NPToolExecutionDescriptionSummary(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example_2"),
            3L
          ),
          NPToolName.of("com.io7m.tool_2"),
          "A description."
        )
      ),
      p.items()
    );
  }

  /**
   * Deleting referenced tool executions works as expected.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecIntegrity0()
    throws Exception
  {
    final var planPut =
      this.transaction.queries(NPDatabaseQueriesPlansType.PlanPutType.class);
    final var put =
      this.transaction.queries(PutExecutionDescriptionType.class);
    final var delete =
      this.transaction.queries(DeleteExecutionDescriptionType.class);

    final var tool =
      new NPToolExecutionDescription(
        new NPToolExecutionIdentifier(
          NPToolExecutionName.of("com.io7m.example"),
          23L
        ),
        NPToolName.of("com.io7m.tool"),
        "A description.",
        NPFormatName.of("com.io7m.northpike.toolexec.js"),
        "execution.argumentAdd('ok')"
      );

    put.execute(tool);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final var planBuilder =
      NPPlans.builder(strings, "com.io7m.p", 1L);

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
          tool.identifier(),
          Set.of()
        )
      );

    final var plan =
      planBuilder.build();

    planPut.execute(new Parameters(plan, new NPPlanSerializers()));

    final var ex =
      assertThrows(NPDatabaseException.class, () -> {
        delete.execute(tool.identifier());
      });

    assertEquals(errorToolExecutionStillReferenced(), ex.errorCode());
  }
}
