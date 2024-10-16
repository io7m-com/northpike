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
import com.io7m.northpike.database.api.NPCommitSummaryLinkedPagedType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesPublicKeysType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryCommitsPutType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryPublicKeyAssignType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryPublicKeyIsAssignedType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryPublicKeyUnassignType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryPublicKeysAssignedType;
import com.io7m.northpike.database.api.NPDatabaseQueriesSCMProvidersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitGraph;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitLink;
import com.io7m.northpike.model.NPCommitSearchParameters;
import com.io7m.northpike.model.NPCommitSummaryLinked;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPRepositoryCredentialsUsernamePassword;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.model.NPTimeRange;
import com.io7m.northpike.tests.containers.NPDatabaseFixture;
import com.io7m.northpike.tests.containers.NPFixtures;
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
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Optional;
import java.util.Set;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPRepositoryCredentialsNone.CREDENTIALS_NONE;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabaseRepositoriesTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPDatabaseRepositoriesTest.class);

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
   * Creating repositories works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryCreate0()
    throws Exception
  {
    final var putSCM =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.SCMProviderPutType.class);
    final var get =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryGetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A provider.",
        URI.create("https://www.example.com/scm")
      );

    final var description =
      new NPRepositoryDescription(
        scm.name(),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    putSCM.execute(scm);
    put.execute(description);
    assertEquals(description, get.execute(description.id()).orElseThrow());
  }

  /**
   * Creating repositories fails for nonexistent SCM providers.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryCreateBadSCM0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryGetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class);

    final var description =
      new NPRepositoryDescription(
        new RDottedName("x.y"),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        put.execute(description);
      });
    assertEquals(errorNonexistent(), ex.errorCode());
  }

  /**
   * Nonexistent repositories are nonexistent.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryGet0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryGetType.class);

    assertEquals(
      Optional.empty(),
      get.execute(new NPRepositoryID(randomUUID()))
    );
  }

  /**
   * Creating repository commits works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryCommits0()
    throws Exception
  {
    final var putSCM =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.SCMProviderPutType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class);
    final var putCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsPutType.class);
    final var getCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsGetType.class);
    final var getCommit =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitGetType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A provider.",
        URI.create("https://www.example.com/scm")
      );

    final var repository =
      new NPRepositoryDescription(
        scm.name(),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    putSCM.execute(scm);
    put.execute(repository);

    final var generated =
      generateFakeCommits(repository.id());

    putCommits.execute(
      new Parameters(
        Set.copyOf(generated.commits),
        generated.graph
      )
    );

    this.transaction.commit();

    for (final var c : generated.commits) {
      assertEquals(c, getCommit.execute(c.id()).orElseThrow());
    }

    final var paged =
      getCommits.execute(
        new NPCommitSearchParameters(
          Optional.empty(),
          Optional.empty(),
          Optional.empty(),
          NPTimeRange.largest(),
          NPTimeRange.largest(),
          50L
        )
      );

    this.dumpAllPages(paged);

    final NPPage<NPCommitSummaryLinked> pageCurrent =
      paged.pageCurrent(this.transaction);

    assertEquals(1L, (long) pageCurrent.pageIndex());
    assertEquals(3L, (long) pageCurrent.pageCount());
    assertEquals(0L, pageCurrent.pageFirstOffset());
    assertEquals(50L, (long) pageCurrent.items().size());
  }

  /**
   * Searching by time works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryCommits3()
    throws Exception
  {
    final var putSCM =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.SCMProviderPutType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class);
    final var putCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsPutType.class);
    final var getCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsGetType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A provider.",
        URI.create("https://www.example.com/scm")
      );

    final var repository =
      new NPRepositoryDescription(
        scm.name(),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    putSCM.execute(scm);
    put.execute(repository);

    final var generated =
      generateFakeCommits(repository.id());

    putCommits.execute(
      new Parameters(
        Set.copyOf(generated.commits),
        generated.graph
      )
    );

    this.transaction.commit();

    final var paged =
      getCommits.execute(
        new NPCommitSearchParameters(
          Optional.empty(),
          Optional.empty(),
          Optional.empty(),
          new NPTimeRange(
            generated.commits.get(75).timeCreated(),
            NPTimeRange.largest().upper()
          ),
          NPTimeRange.largest(),
          50L
        )
      );

    this.dumpAllPages(paged);

    final NPPage<NPCommitSummaryLinked> pageCurrent =
      paged.pageCurrent(this.transaction);

    assertEquals(1L, (long) pageCurrent.pageIndex());
    assertEquals(1L, (long) pageCurrent.pageCount());
    assertEquals(0L, pageCurrent.pageFirstOffset());
    assertEquals(25L, (long) pageCurrent.items().size());
  }

  /**
   * Searching by time works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryCommits4()
    throws Exception
  {
    final var putSCM =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.SCMProviderPutType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class);
    final var putCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsPutType.class);
    final var getCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsGetType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A provider.",
        URI.create("https://www.example.com/scm")
      );

    final var repository =
      new NPRepositoryDescription(
        scm.name(),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    putSCM.execute(scm);
    put.execute(repository);

    final var generated =
      generateFakeCommits(repository.id());

    putCommits.execute(
      new Parameters(
        Set.copyOf(generated.commits),
        generated.graph
      )
    );

    this.transaction.commit();

    final var paged =
      getCommits.execute(
        new NPCommitSearchParameters(
          Optional.empty(),
          Optional.empty(),
          Optional.empty(),
          NPTimeRange.largest(),
          new NPTimeRange(
            generated.commits.get(75).timeReceived(),
            NPTimeRange.largest().upper()
          ),
          50L
        )
      );

    this.dumpAllPages(paged);

    final NPPage<NPCommitSummaryLinked> pageCurrent =
      paged.pageCurrent(this.transaction);

    assertEquals(1L, (long) pageCurrent.pageIndex());
    assertEquals(1L, (long) pageCurrent.pageCount());
    assertEquals(0L, pageCurrent.pageFirstOffset());
    assertEquals(25L, (long) pageCurrent.items().size());
  }

  /**
   * Searching "since commit" works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryCommits5()
    throws Exception
  {
    final var putSCM =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.SCMProviderPutType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class);
    final var putCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsPutType.class);
    final var getCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsGetType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A provider.",
        URI.create("https://www.example.com/scm")
      );

    final var repository =
      new NPRepositoryDescription(
        scm.name(),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    putSCM.execute(scm);
    put.execute(repository);

    final var generated =
      generateFakeCommits(repository.id());

    putCommits.execute(
      new Parameters(
        Set.copyOf(generated.commits),
        generated.graph
      )
    );

    this.transaction.commit();

    final var paged =
      getCommits.execute(
        new NPCommitSearchParameters(
          Optional.empty(),
          Optional.of(generated.commits.get(30).id()),
          Optional.empty(),
          NPTimeRange.largest(),
          NPTimeRange.largest(),
          50L
        )
      );

    this.dumpAllPages(paged);

    final NPPage<NPCommitSummaryLinked> pageCurrent =
      paged.pageCurrent(this.transaction);

    assertEquals(1L, (long) pageCurrent.pageIndex());
    assertEquals(2L, (long) pageCurrent.pageCount());
    assertEquals(0L, pageCurrent.pageFirstOffset());
    assertEquals(50L, (long) pageCurrent.items().size());
  }

  /**
   * Searching "since commit" works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryCommits6()
    throws Exception
  {
    final var putSCM =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.SCMProviderPutType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class);
    final var putCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsPutType.class);
    final var getCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsGetType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A provider.",
        URI.create("https://www.example.com/scm")
      );

    final var repository =
      new NPRepositoryDescription(
        scm.name(),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    putSCM.execute(scm);
    put.execute(repository);

    final var generated =
      generateFakeCommits(repository.id());

    putCommits.execute(
      new Parameters(
        Set.copyOf(generated.commits),
        generated.graph
      )
    );

    this.transaction.commit();

    final var paged =
      getCommits.execute(
        new NPCommitSearchParameters(
          Optional.empty(),
          Optional.empty(),
          Optional.of(generated.commits.get(30).id()),
          NPTimeRange.largest(),
          NPTimeRange.largest(),
          50L
        )
      );

    this.dumpAllPages(paged);

    final NPPage<NPCommitSummaryLinked> pageCurrent =
      paged.pageCurrent(this.transaction);

    assertEquals(1L, (long) pageCurrent.pageIndex());
    assertEquals(2L, (long) pageCurrent.pageCount());
    assertEquals(0L, pageCurrent.pageFirstOffset());
    assertEquals(50L, (long) pageCurrent.items().size());
  }

  /**
   * Creating repository commits fails if the repository doesn't exist.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryCommitsNoRepository()
    throws Exception
  {
    final var putCommits =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryCommitsPutType.class);

    final var commit =
      new NPCommit(
        new NPCommitID(new NPRepositoryID(randomUUID()), new NPCommitUnqualifiedID("a")),
        OffsetDateTime.now(),
        OffsetDateTime.now(),
        new NPCommitAuthor(
          "Author",
          "author@example.com"
        ),
        "Subject",
        "Body",
        Set.of("branch"),
        Set.of()
      );

    final var graph =
      NPCommitGraph.create(Set.of());

    final var ex =
      assertThrows(NPDatabaseException.class, () -> {
        putCommits.execute(
          new Parameters(
            Set.of(commit),
            graph
          )
        );
      });

    assertEquals(errorNonexistent(), ex.errorCode());
  }

  /**
   * Listing repositories works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryList0()
    throws Exception
  {
    final var putSCM =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.SCMProviderPutType.class);
    final var list =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryListType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A provider.",
        URI.create("https://www.example.com/scm")
      );

    putSCM.execute(scm);

    final var usernamePassword =
      new NPRepositoryCredentialsUsernamePassword(
        "example", "12345678"
      );

    for (int index = 0; index < 1000; ++index) {
      final var description =
        new NPRepositoryDescription(
          scm.name(),
          new NPRepositoryID(randomUUID()),
          URI.create("https://www.example.com/%04d".formatted(index)),
          index % 2 == 0 ? CREDENTIALS_NONE : usernamePassword,
          ALLOW_UNSIGNED_COMMITS
        );

      put.execute(description);
    }

    this.transaction.commit();

    final var paged =
      list.execute(NPDatabaseUnit.UNIT);

    var uriIndex = 0;
    for (int pageIndex = 0; pageIndex < 10; ++pageIndex) {
      final var page =
        paged.pageCurrent(this.transaction);

      for (int index = 0; index < 100; ++index) {
        final var uri =
          URI.create("https://www.example.com/%04d".formatted(uriIndex));
        final var item =
          page.items().get(index);

        if (uriIndex % 2 == 0) {
          assertEquals(CREDENTIALS_NONE, item.credentials());
        } else {
          assertEquals(usernamePassword, item.credentials());
        }

        assertEquals(uri, item.url());
        ++uriIndex;
      }

      paged.pageNext(this.transaction);
    }
  }

  private void dumpAllPages(
    final NPCommitSummaryLinkedPagedType paged)
    throws NPDatabaseException
  {
    NPPage<NPCommitSummaryLinked> pageCurrent =
      paged.pageCurrent(this.transaction);

    for (int index = 1; index <= pageCurrent.pageCount(); ++index) {
      for (final var item : pageCurrent.items()) {
        LOG.debug(
          "[{}/{}] {} -> {} ({})",
          Integer.valueOf(index),
          Integer.valueOf(pageCurrent.pageCount()),
          item.link().commit(),
          item.link().next(),
          item.commit().messageSubject()
        );
      }
      pageCurrent = paged.pageNext(this.transaction);
    }

    for (int index = pageCurrent.pageCount(); index >= 1; --index) {
      for (final var item : pageCurrent.items()) {
        LOG.debug(
          "[{}/{}] {} -> {} ({})",
          Integer.valueOf(index),
          Integer.valueOf(pageCurrent.pageCount()),
          item.link().commit(),
          item.link().next(),
          item.commit().messageSubject()
        );
      }
      pageCurrent = paged.pagePrevious(this.transaction);
    }
  }

  private static GeneratedCommits generateFakeCommits(
    final NPRepositoryID repository)
    throws NPException
  {
    final var startTime =
      OffsetDateTime.now();
    final var commits =
      new LinkedList<NPCommit>();

    final var author0 =
      new NPCommitAuthor(
        "Author 0",
        "author0@example.com"
      );

    final var author1 =
      new NPCommitAuthor(
        "Author 1",
        "author1@example.com"
      );

    for (int index = 0; index < 100; ++index) {
      final var commit = new NPCommit(
        new NPCommitID(
          repository,
          new NPCommitUnqualifiedID(String.format(
            "%x",
            Integer.valueOf(index)))),
        startTime.plusHours(index).withNano(0),
        startTime.plusHours(index).minusYears(1L).withNano(0),
        index % 3 == 0 ? author1 : author0,
        "Commit " + index,
        "",
        Set.of("develop"),
        Set.of("Tag-" + index, "TagX-" + index)
      );
      commits.add(commit);
    }

    final var links = new HashSet<NPCommitLink>(commits.size());
    for (final var commit : commits) {
      final var next =
        commits.indexOf(commit) + 1;

      final Optional<NPCommitID> nextCommit;
      if (next < commits.size()) {
        nextCommit = Optional.of(commits.get(next).id());
      } else {
        nextCommit = Optional.empty();
      }

      links.add(new NPCommitLink(commit.id(), nextCommit));
    }

    return new GeneratedCommits(commits, NPCommitGraph.create(links));
  }

  record GeneratedCommits(
    LinkedList<NPCommit> commits,
    NPCommitGraph graph)
  {

  }

  /**
   * Assigning keys to repositories works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryKeyAssign()
    throws Exception
  {
    final var putSCM =
      this.transaction.queries(NPDatabaseQueriesSCMProvidersType.SCMProviderPutType.class);
    final var get =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryGetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class);
    final var keyPut =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.PublicKeyPutType.class);

    final var keysAssigned =
      this.transaction.queries(RepositoryPublicKeysAssignedType.class);
    final var keyAssign =
      this.transaction.queries(RepositoryPublicKeyAssignType.class);
    final var keyUnassign =
      this.transaction.queries(RepositoryPublicKeyUnassignType.class);
    final var keyIsAssigned =
      this.transaction.queries(RepositoryPublicKeyIsAssignedType.class);

    final var scm =
      new NPSCMProviderDescription(
        new RDottedName("x.y"),
        "A provider.",
        URI.create("https://www.example.com/scm")
      );

    final var description =
      new NPRepositoryDescription(
        scm.name(),
        new NPRepositoryID(randomUUID()),
        URI.create("https://www.example.com"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    putSCM.execute(scm);
    put.execute(description);

    final var expected =
      new HashSet<NPFingerprint>();

    for (int index = 0; index < 9; ++index) {
      final var keyId =
        new NPFingerprint("f572d396fae9206628714fb2ce00f72e94f2258" + index);

      expected.add(keyId);

      keyPut.execute(
        new NPPublicKey(
          Set.of("Example " + index),
          keyId,
          OffsetDateTime.now().withNano(0),
          Optional.empty(),
          """
            -----BEGIN PGP PUBLIC KEY BLOCK-----
  
            mDMEZQ2b3BYJKwYBBAHaRw8BAQdAlyurVHs8w5+VvhGU6++xmsQCfc+35lYZro0O
            ugEroKu0J0V4YW1wbGUgKEV4YW1wbGUpIDxleGFtcGxlQGV4YW1wbGUuY29tPoiW
            BBMWCAA+FiEEL6HX/r/nWP/p+Rtf926L7eldjOEFAmUNm9wCGwMFCTPoWgAFCwkI
            BwMFFQoJCAsFFgIDAQACHgECF4AACgkQ926L7eldjOEclAEA2DG7KtzQ7A6tDQP3
            pbXiNwK8fuMXR8ALJ01z9dDsPLgA/2wlWC/TAFuG7AdAvWfEU4U6snFDayz8YPot
            zA1rFJcI
            =bfKj
            -----END PGP PUBLIC KEY BLOCK-----
                      """
        )
      );

      assertFalse(keyIsAssigned.execute(
        new RepositoryPublicKeyIsAssignedType.Parameters(description.id(), keyId)
      ).booleanValue());

      keyAssign.execute(
        new RepositoryPublicKeyAssignType.Parameters(description.id(), keyId)
      );

      assertTrue(keyIsAssigned.execute(
        new RepositoryPublicKeyIsAssignedType.Parameters(description.id(), keyId)
      ).booleanValue());

      keyUnassign.execute(
        new RepositoryPublicKeyUnassignType.Parameters(description.id(), keyId)
      );

      assertFalse(keyIsAssigned.execute(
        new RepositoryPublicKeyIsAssignedType.Parameters(description.id(), keyId)
      ).booleanValue());

      keyAssign.execute(
        new RepositoryPublicKeyAssignType.Parameters(description.id(), keyId)
      );
    }

    final var keys =
      keysAssigned.execute(description.id());

    assertEquals(expected, keys);
  }
}
