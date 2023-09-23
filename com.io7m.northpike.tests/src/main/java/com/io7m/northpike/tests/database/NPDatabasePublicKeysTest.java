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
import com.io7m.northpike.database.api.NPDatabaseQueriesPublicKeysType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPPublicKeySearchParameters;
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

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.time.OffsetDateTime;
import java.util.HashSet;
import java.util.HexFormat;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabasePublicKeysTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPDatabasePublicKeysTest.class);

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

    this.transaction.setOwner(
      NPTestContainers.NPDatabaseFixture.createUser(
        this.transaction,
        UUID.randomUUID()
      )
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

    final var description =
      new NPPublicKey(
        Set.of("Example (Example) <example@example.com>"),
        new NPFingerprint("2fa1d7febfe758ffe9f91b5ff76e8bede95d8ce1"),
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
      );

    put.execute(description);
    assertEquals(description, get.execute(description.fingerprint()).orElseThrow());

    put.execute(description);
    assertEquals(description, get.execute(description.fingerprint()).orElseThrow());
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

    for (int index = 0; index < 1000; ++index) {
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
        );

      put.execute(description);
    }

    this.transaction.commit();

    final var paged =
      list.execute(new NPPublicKeySearchParameters(100L));

    final var ids = new HashSet<String>();
    for (int pageIndex = 0; pageIndex < 10; ++pageIndex) {
      final var page =
        paged.pageCurrent(this.transaction);
      for (final var item : page.items()) {
        ids.addAll(item.userIDs());
      }
      paged.pageNext(this.transaction);
    }

    for (int index = 0; index < 1000; ++index) {
      assertTrue(ids.contains(Integer.toUnsignedString(index)));
    }
  }
}
