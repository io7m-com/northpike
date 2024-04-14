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
import com.io7m.northpike.database.api.NPDatabaseQueriesPublicKeysType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryPublicKeyAssignType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryPublicKeyIsAssignedType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPPublicKeySearchParameters;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPRepositorySigningPolicy;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
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

import java.io.IOException;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.OffsetDateTime;
import java.util.HashSet;
import java.util.HexFormat;
import java.util.Optional;
import java.util.Properties;
import java.util.Set;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabasePublicKeysTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPDatabasePublicKeysTest.class);

  private static final String KEY_TEXT = """
    -----BEGIN PGP PUBLIC KEY BLOCK-----
      
    mDMEZQ2b3BYJKwYBBAHaRw8BAQdAlyurVHs8w5+VvhGU6++xmsQCfc+35lYZro0O
    ugEroKu0J0V4YW1wbGUgKEV4YW1wbGUpIDxleGFtcGxlQGV4YW1wbGUuY29tPoiW
    BBMWCAA+FiEEL6HX/r/nWP/p+Rtf926L7eldjOEFAmUNm9wCGwMFCTPoWgAFCwkI
    BwMFFQoJCAsFFgIDAQACHgECF4AACgkQ926L7eldjOEclAEA2DG7KtzQ7A6tDQP3
    pbXiNwK8fuMXR8ALJ01z9dDsPLgA/2wlWC/TAFuG7AdAvWfEU4U6snFDayz8YPot
    zA1rFJcI
    =bfKj
    -----END PGP PUBLIC KEY BLOCK-----
              """;

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
   * Creating keys works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPublicKeyCreate0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.PutType.class);
    final var delete =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.DeleteType.class);

    final var description =
      new NPPublicKey(
        Set.of("Example (Example) <example@example.com>"),
        new NPFingerprint("2fa1d7febfe758ffe9f91b5ff76e8bede95d8ce1"),
        OffsetDateTime.now().withNano(0),
        Optional.empty(),
        KEY_TEXT
      );

    put.execute(description);
    assertEquals(description, get.execute(description.fingerprint()).orElseThrow());

    put.execute(description);
    assertEquals(description, get.execute(description.fingerprint()).orElseThrow());

    delete.execute(description.fingerprint());
    assertEquals(Optional.empty(), get.execute(description.fingerprint()));
  }

  /**
   * Nonexistent keys are nonexistent.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPublicKeyGet0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.GetType.class);

    assertEquals(
      Optional.empty(),
      get.execute(new NPFingerprint("2fa1d7febfe758ffe9f91b5ff76e8bede95d8ce1"))
    );
  }

  /**
   * Assigned keys can be deleted.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPublicKeyAssignedDelete()
    throws Exception
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.PutType.class);
    final var delete =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.DeleteType.class);

    final var reposPut =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class);
    final var reposKeyAssign =
      this.transaction.queries(RepositoryPublicKeyAssignType.class);
    final var reposKeyAssigned =
      this.transaction.queries(RepositoryPublicKeyIsAssignedType.class);

    final var description =
      new NPPublicKey(
        Set.of("Example (Example) <example@example.com>"),
        new NPFingerprint("2fa1d7febfe758ffe9f91b5ff76e8bede95d8ce1"),
        OffsetDateTime.now().withNano(0),
        Optional.empty(),
        KEY_TEXT
      );

    final var repositoryDescription =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        URI.create("http://www.example.com/git0"),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS
      );

    reposPut.execute(repositoryDescription);
    put.execute(description);

    reposKeyAssign.execute(new RepositoryPublicKeyAssignType.Parameters(
      repositoryDescription.id(),
      description.fingerprint()
    ));

    assertTrue(
      reposKeyAssigned.execute(new RepositoryPublicKeyIsAssignedType.Parameters(
        repositoryDescription.id(),
        description.fingerprint()
      )).booleanValue()
    );

    delete.execute(description.fingerprint());

    assertFalse(
      reposKeyAssigned.execute(new RepositoryPublicKeyIsAssignedType.Parameters(
        repositoryDescription.id(),
        description.fingerprint()
      )).booleanValue()
    );
  }

  /**
   * Listing keys works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPublicKeyList0()
    throws Exception
  {
    final var list =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.PutType.class);

    for (var index = 0; index < 1000; ++index) {
      final var data =
        Integer.toUnsignedString(index).getBytes(StandardCharsets.UTF_8);
      final var hash =
        MessageDigest.getInstance("SHA1");

      final var fingerpint =
        new NPFingerprint(
          HexFormat.of().formatHex(hash.digest(data))
        );

      final var description =
        new NPPublicKey(
          Set.of(Integer.toUnsignedString(index)),
          fingerpint,
          OffsetDateTime.now().withNano(0),
          Optional.empty(),
          KEY_TEXT
        );

      put.execute(description);
    }

    this.transaction.commit();

    final var paged =
      list.execute(
        new NPPublicKeySearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          100L
        )
      );

    final var ids = new HashSet<String>();
    for (var pageIndex = 0; pageIndex < 10; ++pageIndex) {
      final var page =
        paged.pageCurrent(this.transaction);
      for (final var item : page.items()) {
        ids.addAll(item.userIDs());
      }
      paged.pageNext(this.transaction);
    }

    for (var index = 0; index < 1000; ++index) {
      assertTrue(ids.contains(Integer.toUnsignedString(index)));
    }
  }

  /**
   * Listing keys works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPublicKeyList1()
    throws Exception
  {
    final var list =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.PutType.class);

    final var words =
      save1000SampleKeys(put);

    this.transaction.commit();

    final var searchWord =
      words.getProperty("500");

    final var paged =
      list.execute(
        new NPPublicKeySearchParameters(
          new NPComparisonFuzzyType.IsEqualTo<>(searchWord),
          100L
        )
      );

    final var page =
      paged.pageCurrent(this.transaction);

    final var item = page.items().get(0);
    assertEquals(Set.of(searchWord), item.userIDs());

    assertEquals(1, page.pageIndex());
    assertEquals(1, page.pageCount());
    assertEquals(1, page.items().size());
  }

  /**
   * Listing keys works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPublicKeyList2()
    throws Exception
  {
    final var list =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.PutType.class);

    final var words =
      save1000SampleKeys(put);

    this.transaction.commit();

    final var searchWord =
      words.getProperty("500");

    final var paged =
      list.execute(
        new NPPublicKeySearchParameters(
          new NPComparisonFuzzyType.IsNotEqualTo<>(searchWord),
          1000L
        )
      );

    final var page =
      paged.pageCurrent(this.transaction);

    assertFalse(
      page.items()
        .stream()
        .anyMatch(key -> key.userIDs().contains(searchWord))
    );

    for (var index = 0; index < 1000; ++index) {
      if (index + 1 == 500) {
        continue;
      }

      final var expectedWord =
        words.getProperty(Integer.toUnsignedString(index + 1));

      assertTrue(
        page.items()
          .stream()
          .anyMatch(key -> key.userIDs().contains(expectedWord))
      );
    }

    assertEquals(1, page.pageIndex());
    assertEquals(1, page.pageCount());
    assertEquals(999, page.items().size());
  }

  /**
   * Listing keys works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPublicKeyList3()
    throws Exception
  {
    final var list =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.PutType.class);

    final var words =
      save1000SampleKeys(put);

    this.transaction.commit();

    final var searchWord =
      words.getProperty("500");

    final var paged =
      list.execute(
        new NPPublicKeySearchParameters(
          new NPComparisonFuzzyType.IsSimilarTo<>(searchWord),
          1000L
        )
      );

    final var page =
      paged.pageCurrent(this.transaction);

    final var item = page.items().get(0);
    assertEquals(Set.of(searchWord), item.userIDs());

    assertEquals(1, page.pageIndex());
    assertEquals(1, page.pageCount());
    assertEquals(1, page.items().size());
  }

  /**
   * Listing keys works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPublicKeyList4()
    throws Exception
  {
    final var list =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.SearchType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesPublicKeysType.PutType.class);

    final var words =
      save1000SampleKeys(put);

    this.transaction.commit();

    final var searchWord =
      words.getProperty("500");

    final var paged =
      list.execute(
        new NPPublicKeySearchParameters(
          new NPComparisonFuzzyType.IsNotSimilarTo<>(searchWord),
          1000L
        )
      );

    final var page =
      paged.pageCurrent(this.transaction);

    assertFalse(
      page.items()
        .stream()
        .anyMatch(key -> key.userIDs().contains(searchWord))
    );

    for (var index = 0; index < 1000; ++index) {
      if (index + 1 == 500) {
        continue;
      }

      final var expectedWord =
        words.getProperty(Integer.toUnsignedString(index + 1));

      assertTrue(
        page.items()
          .stream()
          .anyMatch(key -> key.userIDs().contains(expectedWord))
      );
    }

    assertEquals(1, page.pageIndex());
    assertEquals(1, page.pageCount());
    assertEquals(999, page.items().size());
  }

  private static Properties save1000SampleKeys(
    final NPDatabaseQueriesPublicKeysType.PutType put)
    throws IOException, NoSuchAlgorithmException, NPDatabaseException
  {
    final var words = openWords();
    for (var index = 0; index < 1000; ++index) {
      final var data =
        Integer.toUnsignedString(index).getBytes(StandardCharsets.UTF_8);
      final var hash =
        MessageDigest.getInstance("SHA1");
      final var word =
        words.getProperty(Integer.toUnsignedString(index + 1));

      final var fingerpint =
        new NPFingerprint(
          HexFormat.of().formatHex(hash.digest(data))
        );

      final var description =
        new NPPublicKey(
          Set.of(word),
          fingerpint,
          OffsetDateTime.now().withNano(0),
          Optional.empty(),
          KEY_TEXT
        );

      put.execute(description);
    }
    return words;
  }

  private static Properties openWords()
    throws IOException
  {
    final var properties = new Properties();
    try (var stream = NPDatabasePublicKeysTest.class.getResourceAsStream(
      "/com/io7m/northpike/tests/words.properties"
    )) {
      properties.load(stream);
      return properties;
    }
  }
}
