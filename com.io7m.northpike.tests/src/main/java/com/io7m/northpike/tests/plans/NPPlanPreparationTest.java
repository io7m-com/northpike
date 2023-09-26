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


package com.io7m.northpike.tests.plans;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPArchiveWithLinks;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPHash;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.model.plans.NPPlanToolExecution;
import com.io7m.northpike.plans.NPPlanToolExecutionCompilerType;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.preparation.NPPlanPreparation;
import com.io7m.northpike.plans.variables.NPPlanStandardVariables;
import com.io7m.northpike.plans.variables.NPPlanVariableString;
import com.io7m.northpike.plans.variables.NPPlanVariableStringSet;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.toolexec.checker.NPTXChecker;
import com.io7m.northpike.toolexec.model.NPTXDescription;
import com.io7m.northpike.toolexec.model.NPTXPlanVariables;
import com.io7m.verona.core.Version;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.net.URI;
import java.time.OffsetDateTime;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;

public final class NPPlanPreparationTest
{
  private static final NPCommit COMMIT =
    new NPCommit(
      new NPCommitID(
        new NPRepositoryID(randomUUID()),
        new NPCommitUnqualifiedID("deda21dfcddaf071d42e374db3bf2afc")
      ),
      OffsetDateTime.now(),
      OffsetDateTime.now(),
      new NPCommitAuthor("Author", "someone@example.com"),
      "Subject",
      "Body",
      Set.of("b"),
      Set.of("t")
    );

  private static final NPArchiveWithLinks ARCHIVE =
    new NPArchiveWithLinks(
      new NPArchive(
        new NPToken("cc8ce020992d9d4a1cc83a1ea465d7f5fbe2e54fb3f4c815dc33c236633cb283"),
        COMMIT.id(),
        new NPHash(
          "SHA-256",
          "da28353fcdba28e253da6f2ebfd04058c256addb87005dc8b694ebff17921848"
        ),
        OffsetDateTime.now()
      ),
      new NPArchiveLinks(
        URI.create("https://www.example.com/archive.tgz"),
        URI.create("https://www.example.com/archive.tgz.sha512")
      )
    );

  /**
   * The default plan variables appear in prepared plans.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanVariables()
    throws Exception
  {
    final var resources =
      Mockito.mock(NPPlanToolExecutionCompilerType.class);

    final var plan =
      NPPlans.builder(NPStrings.create(Locale.ROOT), "p", 1L)
        .build();

    final var preparation =
      NPPlanPreparation.forCommit(resources, COMMIT, ARCHIVE, plan);

    assertEquals(Map.of(), preparation.toolExecutions());
    assertEquals(plan, preparation.plan());
    assertEquals(
      "https://www.example.com/archive.tgz",
      ((NPPlanVariableString) preparation.planVariables()
        .variables()
        .get(NPPlanStandardVariables.archiveURL().name()))
        .value()
    );
    assertEquals(
      "https://www.example.com/archive.tgz.sha512",
      ((NPPlanVariableString) preparation.planVariables()
        .variables()
        .get(NPPlanStandardVariables.archiveChecksumURL().name()))
        .value()
    );
    assertEquals(
      COMMIT.id().commitId().value(),
      ((NPPlanVariableString) preparation.planVariables()
        .variables()
        .get(NPPlanStandardVariables.scmCommit().name()))
        .value()
    );
    assertEquals(
      COMMIT.branches(),
      ((NPPlanVariableStringSet) preparation.planVariables()
        .variables()
        .get(NPPlanStandardVariables.scmBranches().name()))
        .value()
    );
  }

  /**
   * Plans cannot be prepared if tool execution compilation fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecutionCompilation()
    throws Exception
  {
    final var resources =
      Mockito.mock(NPPlanToolExecutionCompilerType.class);

    final var planBuilder =
      NPPlans.builder(NPStrings.create(Locale.ROOT), "p", 1L)
        .addToolReference(new NPToolReference(
          NPToolReferenceName.of("t"),
          NPToolName.of("tn"),
          Version.of(1, 0, 0)
        ));

    planBuilder.addTask("t")
      .setToolExecution(new NPPlanToolExecution(
        NPToolReferenceName.of("t"),
        NPToolExecutionIdentifier.of("x", 1L),
        Set.of()
      ));

    final var plan =
      planBuilder.build();

    Mockito.when(resources.toolCompile(any(), any()))
      .thenThrow(new NPPlanException(
        "Tool compilation failed.",
        new NPErrorCode("tool"),
        Map.of(),
        Optional.empty()
      ));

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        NPPlanPreparation.forCommit(resources, COMMIT, ARCHIVE, plan);
      });

    assertEquals("Tool compilation failed.", ex.getMessage());
  }

  /**
   * Plans can be prepared.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecutionOK()
    throws Exception
  {
    final var checked =
      NPTXChecker.checkDescription(
        new NPTXPlanVariables(Map.of()),
        new NPTXDescription(
          new RDottedName("t"),
          1L,
          List.of()
        )
      );

    final var resources =
      Mockito.mock(NPPlanToolExecutionCompilerType.class);

    final var planBuilder =
      NPPlans.builder(NPStrings.create(Locale.ROOT), "p", 1L)
        .addToolReference(new NPToolReference(
          NPToolReferenceName.of("t"),
          NPToolName.of("tn"),
          Version.of(1, 0, 0)
        ));

    final var taskBuilder =
      planBuilder.addTask("t")
        .setToolExecution(new NPPlanToolExecution(
          NPToolReferenceName.of("t"),
          NPToolExecutionIdentifier.of("x", 1L),
          Set.of()
        ));

    final var plan =
      planBuilder.build();

    Mockito.when(resources.toolCompile(any(), any()))
      .thenReturn(checked);

    final var preparation =
      NPPlanPreparation.forCommit(resources, COMMIT, ARCHIVE, plan);

    assertEquals(
      checked,
      preparation.toolExecutions().get(taskBuilder.name())
    );
  }
}
