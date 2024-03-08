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

package com.io7m.northpike.tests.scm_repository;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.clock.NPClock;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
import com.io7m.northpike.scm_repository.spi.NPSCMEventType;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryException;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.apache.commons.compress.archivers.examples.Expander;
import org.apache.commons.compress.archivers.tar.TarArchiveInputStream;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.time.Clock;
import java.time.OffsetDateTime;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.Flow;
import java.util.stream.Collectors;
import java.util.zip.GZIPInputStream;

import static com.io7m.northpike.model.NPRepositoryCredentialsNone.CREDENTIALS_NONE;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class NPSCMRepositoriesJGitTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPSCMRepositoriesJGitTest.class);

  private NPSCMRepositoriesJGit repositories;
  private RPServiceDirectory services;
  private NPStrings strings;

  @BeforeEach
  public void setup()
  {
    this.strings =
      NPStrings.create(Locale.ROOT);
    this.repositories =
      new NPSCMRepositoriesJGit();

    this.services = new RPServiceDirectory();
    this.services.register(NPStrings.class, this.strings);
    this.services.register(
      NPTelemetryServiceType.class,
      NPTelemetryNoOp.noop());
    this.services.register(
      NPClockServiceType.class,
      new NPClock(Clock.systemUTC()));
  }

  /**
   * Passing an empty set of commits returns all commits.
   *
   * @param directory      The directory
   * @param reposDirectory The repos directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testCommitsSinceEmptySet(
    final @TempDir Path directory,
    final @TempDir Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("example.git.tar", reposDirectory);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("com.io7m.northpike.repository.jgit"),
        new NPRepositoryID(randomUUID()),
        reposSource,
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    try (var repository =
           this.repositories.createRepository(
             this.services, directory, repositoryDescription)) {
      repository.events().subscribe(new EventLogger());

      final var commitSet =
        repository.commitsSince(Set.of());

      final var commits = commitSet.commits();
      dumpCommits(commits);
      assertEquals(13, commits.size());

      assertEquals(
        Set.of(
          "f6d27f77259522f10f7062efca687978531456a4",
          "30dfe62404b3f4338297432d95e17b0630d0960c",
          "11e4ee346c9a8708688acc4f32beac8955714b6c",
          "e4b4a304374886824d94b8cdf49d44c76081eeaf",
          "a6f4b51d85271d34e6cd79424416afaf0554d826",
          "b155d186fce6d0525b8348cc48dd778fda6c6a85",
          "5634fee48558be958830b324dd283bbde568aeb4",
          "27b00e3adce185f2b00096894e0b6bf34e9a157f",
          "9141a3dc3b8f0444b61aae7d4f26afcd9b6d7dbd",
          "f512486ea90cab4a8f00bc01f2ba2083f65aa0ab",
          "db164a1037656bfe0f4253bf9ea882ab28696b77",
          "293d2389c729ff9574f55fcb211d4594f14193f2",
          "6cf9c3deec2e9663a204a8ca2c30717ff4366e5d"
        ),
        commits.stream()
          .map(c -> c.id().commitId())
          .map(NPCommitUnqualifiedID::value)
          .collect(Collectors.toUnmodifiableSet())
      );
    }

    try (var repository =
           this.repositories.createRepository(
             this.services, directory, repositoryDescription)) {
      repository.events().subscribe(new EventLogger());

      final var commitSet =
        repository.commitsSince(Set.of());

      final var commits = commitSet.commits();
      dumpCommits(commits);
      assertEquals(13, commits.size());

      assertEquals(
        Set.of(
          "f6d27f77259522f10f7062efca687978531456a4",
          "30dfe62404b3f4338297432d95e17b0630d0960c",
          "11e4ee346c9a8708688acc4f32beac8955714b6c",
          "e4b4a304374886824d94b8cdf49d44c76081eeaf",
          "a6f4b51d85271d34e6cd79424416afaf0554d826",
          "b155d186fce6d0525b8348cc48dd778fda6c6a85",
          "5634fee48558be958830b324dd283bbde568aeb4",
          "27b00e3adce185f2b00096894e0b6bf34e9a157f",
          "9141a3dc3b8f0444b61aae7d4f26afcd9b6d7dbd",
          "f512486ea90cab4a8f00bc01f2ba2083f65aa0ab",
          "db164a1037656bfe0f4253bf9ea882ab28696b77",
          "293d2389c729ff9574f55fcb211d4594f14193f2",
          "6cf9c3deec2e9663a204a8ca2c30717ff4366e5d"
        ),
        commits.stream()
          .map(c -> c.id().commitId())
          .map(NPCommitUnqualifiedID::value)
          .collect(Collectors.toUnmodifiableSet())
      );
    }
  }

  /**
   * Passing a set of commits returns relevant commits.
   *
   * @param directory      The directory
   * @param reposDirectory The repos directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testStartFrom(
    final @TempDir Path directory,
    final @TempDir Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("example.git.tar", reposDirectory);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("com.io7m.northpike.repository.jgit"),
        new NPRepositoryID(randomUUID()),
        reposSource,
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    final var exampleCommit =
      new NPCommitSummary(
        new NPCommitID(
          repositoryDescription.id(),
          new NPCommitUnqualifiedID("f512486ea90cab4a8f00bc01f2ba2083f65aa0ab")
        ),
        OffsetDateTime.parse("2023-07-28T11:12:36+00:00"),
        OffsetDateTime.parse("2023-07-28T11:12:36+00:00"),
        "Update jenkins"
      );

    try (var repository =
           this.repositories.createRepository(
             this.services, directory, repositoryDescription)) {
      repository.events().subscribe(new EventLogger());

      final var commitSet =
        repository.commitsSince(Set.of(exampleCommit));

      final var commits = commitSet.commits();
      dumpCommits(commits);
      assertEquals(9, commits.size());

      assertEquals(
        Set.of(
          "11e4ee346c9a8708688acc4f32beac8955714b6c",
          "27b00e3adce185f2b00096894e0b6bf34e9a157f",
          "30dfe62404b3f4338297432d95e17b0630d0960c",
          "5634fee48558be958830b324dd283bbde568aeb4",
          "9141a3dc3b8f0444b61aae7d4f26afcd9b6d7dbd",
          "a6f4b51d85271d34e6cd79424416afaf0554d826",
          "b155d186fce6d0525b8348cc48dd778fda6c6a85",
          "e4b4a304374886824d94b8cdf49d44c76081eeaf",
          "f6d27f77259522f10f7062efca687978531456a4"
        ),
        commits.stream()
          .map(c -> c.id().commitId())
          .map(NPCommitUnqualifiedID::value)
          .collect(Collectors.toUnmodifiableSet())
      );
    }

    try (var repository =
           this.repositories.createRepository(
             this.services, directory, repositoryDescription)) {
      repository.events().subscribe(new EventLogger());

      final var commitSet =
        repository.commitsSince(Set.of(exampleCommit));

      final var commits = commitSet.commits();
      dumpCommits(commits);
      assertEquals(9, commits.size());

      assertEquals(
        Set.of(
          "11e4ee346c9a8708688acc4f32beac8955714b6c",
          "27b00e3adce185f2b00096894e0b6bf34e9a157f",
          "30dfe62404b3f4338297432d95e17b0630d0960c",
          "5634fee48558be958830b324dd283bbde568aeb4",
          "9141a3dc3b8f0444b61aae7d4f26afcd9b6d7dbd",
          "a6f4b51d85271d34e6cd79424416afaf0554d826",
          "b155d186fce6d0525b8348cc48dd778fda6c6a85",
          "e4b4a304374886824d94b8cdf49d44c76081eeaf",
          "f6d27f77259522f10f7062efca687978531456a4"
        ),
        commits.stream()
          .map(c -> c.id().commitId())
          .map(NPCommitUnqualifiedID::value)
          .collect(Collectors.toUnmodifiableSet())
      );
    }
  }

  /**
   * Corrupt repositories cannot be operated upon.
   *
   * @param directory The directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testCorrupt0(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      Files.writeString(
        directory.resolve("repos.git"), "Not valid!");

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("com.io7m.northpike.repository.jgit"),
        new NPRepositoryID(randomUUID()),
        file.toUri(),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    try (var repository =
           this.repositories.createRepository(
             this.services, directory, repositoryDescription)) {

      final var ex =
        assertThrows(NPSCMRepositoryException.class, () -> {
          repository.commitsSince(Set.of());
        });

      assertEquals(NPStandardErrorCodes.errorIo(), ex.errorCode());
    }
  }

  private static void dumpCommits(
    final Set<NPCommit> commits)
  {
    for (final var commit : commits) {
      LOG.debug(
        "{} {} {}",
        commit.id().commitId(),
        commit.timeCreated(),
        commit.messageSubject()
      );
    }
  }

  public static URI unpack(
    final String name,
    final Path reposDirectory)
    throws Exception
  {
    final var output =
      reposDirectory.resolve("repos.tar");
    final var resourcePath =
      "/com/io7m/northpike/tests/%s".formatted(name);

    try (var input =
           NPSCMRepositoriesJGitTest.class.getResourceAsStream(resourcePath)) {
      if (input == null) {
        throw new FileNotFoundException(resourcePath);
      }
      Files.copy(input, output, StandardCopyOption.REPLACE_EXISTING);
    }

    try (var tarStream =
           new TarArchiveInputStream(Files.newInputStream(output))) {
      while (true) {
        final var entry = tarStream.getNextEntry();
        if (entry == null) {
          break;
        }
        if (entry.isDirectory()) {
          Files.createDirectories(reposDirectory.resolve(entry.getName()));
          continue;
        }
        if (entry.isFile()) {
          Files.copy(tarStream, reposDirectory.resolve(entry.getName()));
          continue;
        }
      }
    }

    return reposDirectory.resolve("repos.git").toUri();
  }

  /**
   * Producing an archive works.
   *
   * @param directory      The directory
   * @param reposDirectory The repos directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testArchive0(
    final @TempDir Path directory,
    final @TempDir Path outputDirectory,
    final @TempDir Path expandDirectory,
    final @TempDir Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("example.git.tar", reposDirectory);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("com.io7m.northpike.repository.jgit"),
        new NPRepositoryID(randomUUID()),
        reposSource,
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    final var fileTmp =
      outputDirectory.resolve("archive.tgz.tmp");
    final var file =
      outputDirectory.resolve("archive.tgz");
    final var checksumTmp =
      outputDirectory.resolve("archive.tgz.sha256.tmp");
    final var checksum =
      outputDirectory.resolve("archive.tgz.sha256");

    try (var repository =
           this.repositories.createRepository(
             this.services, directory, repositoryDescription)) {
      repository.events().subscribe(new EventLogger());
      repository.commitArchive(
        new NPCommitID(
          repositoryDescription.id(),
          new NPCommitUnqualifiedID("b155d186fce6d0525b8348cc48dd778fda6c6a85")
        ),
        new NPToken(
          "0000000000000000000000000000000000000000000000000000000000000000"),
        file,
        fileTmp,
        checksum,
        checksumTmp
      );

      assertTrue(Files.isRegularFile(file));
      assertFalse(Files.isRegularFile(fileTmp));

      expandArchive(expandDirectory, file);
      assertTrue(Files.isRegularFile(expandDirectory.resolve(".gitmodules")));
      assertTrue(Files.isDirectory(expandDirectory.resolve(".jenkins")));
      assertTrue(Files.isRegularFile(expandDirectory.resolve("pom.xml")));
    }
  }

  /**
   * Verifying commit signatures works.
   *
   * @param directory      The directory
   * @param reposDirectory The repos directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testCommitSign(
    final @TempDir Path directory,
    final @TempDir Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("demo.git.tar", reposDirectory);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("com.io7m.northpike.repository.jgit"),
        new NPRepositoryID(randomUUID()),
        reposSource,
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    try (var repository =
           this.repositories.createRepository(
             this.services, directory, repositoryDescription)) {

      repository.commitVerifySignature(
        new NPCommitUnqualifiedID("cde3f73fa34459a7f9a2b2734636bbe9bdebe5ac"),
        fingerprint -> PUBLIC_KEY_0
      );
    }
  }

  /**
   * A "bad" commit signature cannot be verified. This test emulates a bad
   * signature by deliberately passing the wrong key to the verification
   * function.
   *
   * @param directory      The directory
   * @param reposDirectory The repos directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testCommitSignInvalid(
    final @TempDir Path directory,
    final @TempDir Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("demo.git.tar", reposDirectory);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("com.io7m.northpike.repository.jgit"),
        new NPRepositoryID(randomUUID()),
        reposSource,
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    try (var repository =
           this.repositories.createRepository(
             this.services, directory, repositoryDescription)) {

      assertThrows(NPSCMRepositoryException.class, () -> {
        repository.commitVerifySignature(
          new NPCommitUnqualifiedID("cde3f73fa34459a7f9a2b2734636bbe9bdebe5ac"),
          fingerprint -> {
            return new NPPublicKey(
              PUBLIC_KEY_1.userIDs(),
              PUBLIC_KEY_0.fingerprint(),
              PUBLIC_KEY_1.timeCreated(),
              PUBLIC_KEY_1.timeExpires(),
              PUBLIC_KEY_1.encodedForm()
            );
          }
        );
      });
    }
  }

  /**
   * Unsigned commits cannot be verified.
   *
   * @param directory      The directory
   * @param reposDirectory The repos directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testCommitUnsigned(
    final @TempDir Path directory,
    final @TempDir Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("demo.git.tar", reposDirectory);

    final var repositoryDescription =
      new NPRepositoryDescription(
        new RDottedName("com.io7m.northpike.repository.jgit"),
        new NPRepositoryID(randomUUID()),
        reposSource,
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    try (var repository =
           this.repositories.createRepository(
             this.services, directory, repositoryDescription)) {

      assertThrows(NPSCMRepositoryException.class, () -> {
        repository.commitVerifySignature(
          new NPCommitUnqualifiedID("82fa7441887fa2c57d2dea604f9aef1525b7f54f"),
          fingerprint -> PUBLIC_KEY_0
        );
      });
    }
  }

  private static final NPPublicKey PUBLIC_KEY_0 =
    new NPPublicKey(
      Set.of(
        "Northpike (Northpike Example Key) <noone@example.com>"
      ),
      new NPFingerprint("10ff1ed0241c1fd72590facf3d3dab4fb3cc298b"),
      OffsetDateTime.now(),
      Optional.empty(),
      """
        -----BEGIN PGP PUBLIC KEY BLOCK-----

        mDMEZQ37xRYJKwYBBAHaRw8BAQdA7He9A88wApW0TPahm8XJqywfLph/fmgCOEFr
        Tz6sNWK0NU5vcnRocGlrZSAoTm9ydGhwaWtlIEV4YW1wbGUgS2V5KSA8bm9vbmVA
        ZXhhbXBsZS5jb20+iJAEExYIADgWIQQQ/x7QJBwf1yWQ+s89PatPs8wpiwUCZQ37
        xQIbAwULCQgHAwUVCgkICwUWAgMBAAIeAQIXgAAKCRA9PatPs8wpi2cMAPwOUK7P
        Atq0lGG+8xhk6BKLIs6w2649YQ2Vuup5msFmPgEApqqMV2N1R3IMG5XK6f8vsaqD
        u2zAEQx7OnSnnEETOgI=
        =T6/h
        -----END PGP PUBLIC KEY BLOCK-----
              """
    );

  private static final NPPublicKey PUBLIC_KEY_1 =
    new NPPublicKey(
      Set.of(
        "Northpike (Northpike Example Key 2) <noone@example.com>"
      ),
      new NPFingerprint("0f9aa2c937036ba634d186bd13be2c5148398745"),
      OffsetDateTime.now(),
      Optional.empty(),
      """
-----BEGIN PGP PUBLIC KEY BLOCK-----

mDMEZQ4TaBYJKwYBBAHaRw8BAQdAMNgv7poctgUe5VlVqPF832sXIZdqV139e/IP
ds8SwFa0QU5vcnRocGlrZSAoTm9ydGhwaWtlIEV4YW1wbGUgS2V5IEFsdGVybmF0
aXZlKSA8bm9vbmVAZXhhbXBsZS5jb20+iJAEExYIADgWIQQPmqLJNwNrpjTRhr0T
vixRSDmHRQUCZQ4TaAIbAwULCQgHAwUVCgkICwUWAgMBAAIeAQIXgAAKCRATvixR
SDmHRZGoAQChIyLkA4TIQ6ROdJWrCgSYj0r63zu3y47wqI5U8dXjiAD/WQ3E+FA7
WDQ4AgI9+C5Ommu8ftVPDj7dctHMEl5xEAM=
=zTld
-----END PGP PUBLIC KEY BLOCK-----
              """
    );

  private static void expandArchive(
    final Path expandDirectory,
    final Path file)
    throws IOException
  {
    try (var stream = new GZIPInputStream(Files.newInputStream(file))) {
      try (var tar = new TarArchiveInputStream(stream)) {
        final var expander = new Expander();
        expander.expand(tar, expandDirectory);
      }
    }
  }

  private static final class EventLogger
    implements Flow.Subscriber<NPSCMEventType>
  {
    private Flow.Subscription subscription;

    @Override
    public void onSubscribe(
      final Flow.Subscription inSubscription)
    {
      this.subscription = inSubscription;
      this.subscription.request(Long.MAX_VALUE);
    }

    @Override
    public void onNext(
      final NPSCMEventType item)
    {
      LOG.debug("{}", item);
    }

    @Override
    public void onError(
      final Throwable throwable)
    {
      LOG.error("", throwable);
    }

    @Override
    public void onComplete()
    {

    }
  }
}
