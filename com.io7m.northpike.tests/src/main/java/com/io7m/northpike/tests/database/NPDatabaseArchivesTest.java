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
import com.io7m.northpike.database.api.NPDatabaseQueriesArchivesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesSCMProvidersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitGraph;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPHash;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.tests.containers.NPTestContainerInstances;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.net.URI;
import java.time.OffsetDateTime;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPRepositoryCredentialsNone.CREDENTIALS_NONE;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static org.junit.jupiter.api.Assertions.assertEquals;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabaseArchivesTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPDatabaseArchivesTest.class);

  private static NPTestContainers.NPDatabaseFixture DATABASE_FIXTURE;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPDatabaseType database;

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
  }

  /**
   * Creating archives works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testArchiveCreate0()
    throws Exception
  {
    final var putSCM =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class);
    final var putRepos =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class);
    final var putCommit =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.CommitsPutType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesArchivesType.PutType.class);
    final var get =
      this.transaction.queries(NPDatabaseQueriesArchivesType.GetType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A provider.",
        URI.create("https://www.example.com/scm")
      );

    final var description =
      new NPRepositoryDescription(
        scm.name(),
        UUID.randomUUID(),
        URI.create("https://www.example.com"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    final var commit =
      new NPCommit(
        new NPCommitID(
          description.id(),
          new NPCommitUnqualifiedID("2215f4104678281140622c1088785093319ddc791d11f80cf687d9d4e24e200e")
        ),
        OffsetDateTime.now(),
        OffsetDateTime.now(),
        new NPCommitAuthor("A", "e"),
        "Subject",
        "Body",
        Set.of(),
        Set.of()
      );

    putSCM.execute(scm);
    putRepos.execute(description);
    putCommit.execute(
      new NPDatabaseQueriesRepositoriesType.CommitsPutType.Parameters(
        Set.of(commit),
        NPCommitGraph.create(Set.of())
      )
    );

    final var archive =
      new NPArchive(
        new NPToken(
          "8e35c2cd3bf6641bdb0e2050b76932cbb2e6034a0ddacc1d9bea82a6ba57f7cf"),
        commit.id(),
        new NPHash(
          "SHA-256",
          "454349e422f05297191ead13e21d3db520e5abef52055e4964b82fb213f593a1"
        ),
        OffsetDateTime.now()
          .withNano(0)
      );

    put.execute(archive);

    assertEquals(
      archive,
      get.execute(archive.token()).orElseThrow()
    );
  }

  /**
   * Nonexistent archives are nonexistent.
   *
   * @throws Exception On errors
   */

  @Test
  public void testArchiveGet0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesArchivesType.GetType.class);

    assertEquals(
      Optional.empty(),
      get.execute(
        new NPToken(
          "2215f4104678281140622c1088785093319ddc791d11f80cf687d9d4e24e200e")
      )
    );
  }
}
