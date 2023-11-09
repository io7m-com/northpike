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


package com.io7m.northpike.tests.server.repository;

import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.ervilla.test_extension.ErvillaCloseAfterSuite;
import com.io7m.ervilla.test_extension.ErvillaConfiguration;
import com.io7m.ervilla.test_extension.ErvillaExtension;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.clock.NPClock;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesSCMProvidersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.postgres.NPPGDatabases;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryFactoryType;
import com.io7m.northpike.server.api.NPServerAgentConfiguration;
import com.io7m.northpike.server.api.NPServerArchiveConfiguration;
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.api.NPServerDirectoryConfiguration;
import com.io7m.northpike.server.api.NPServerIdstoreConfiguration;
import com.io7m.northpike.server.api.NPServerMaintenanceConfiguration;
import com.io7m.northpike.server.api.NPServerUserConfiguration;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.events.NPEventService;
import com.io7m.northpike.server.internal.metrics.NPMetricsServiceType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryArchiveCreated;
import com.io7m.northpike.server.internal.repositories.NPRepositoryConfigureFailed;
import com.io7m.northpike.server.internal.repositories.NPRepositoryConfigured;
import com.io7m.northpike.server.internal.repositories.NPRepositoryService;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceStarted;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryUpdateFailed;
import com.io7m.northpike.server.internal.repositories.NPRepositoryUpdated;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.tests.NPEventInterceptingService;
import com.io7m.northpike.tests.containers.NPTestContainerInstances;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.repetoir.core.RPServiceDirectory;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.api.io.TempDir;
import org.mockito.Mockito;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.net.InetAddress;
import java.net.URI;
import java.nio.file.Path;
import java.time.Clock;
import java.time.Duration;
import java.util.Locale;
import java.util.Optional;
import java.util.concurrent.TimeUnit;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static com.io7m.northpike.model.tls.NPTLSDisabled.TLS_DISABLED;
import static com.io7m.northpike.tests.scm_repository.NPSCMRepositoriesJGitTest.unpack;
import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPRepositoryServiceTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPRepositoryServiceTest.class);

  private RPServiceDirectory services;
  private NPClockServiceType clock;
  private NPConfigurationServiceType configuration;
  private NPStrings strings;
  private NPTelemetryNoOp telemetry;
  private NPEventInterceptingService events;
  private NPMetricsServiceType metrics;
  private NPRepositoryServiceType service;

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
    final CloseableResourcesType closeables,
    final @TempDir Path reposDirectory,
    final @TempDir Path archiveDirectory)
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
        randomUUID()
      )
    );

    this.services =
      new RPServiceDirectory();
    this.clock =
      new NPClock(Clock.systemUTC());
    this.configuration =
      Mockito.mock(NPConfigurationServiceType.class);
    this.strings =
      NPStrings.create(Locale.ROOT);
    this.telemetry =
      NPTelemetryNoOp.noop();
    this.events =
      new NPEventInterceptingService(
        NPEventService.create(NPTelemetryNoOp.noop())
      );
    this.metrics =
      Mockito.mock(NPMetricsServiceType.class);

    this.services.register(
      NPClockServiceType.class, this.clock);
    this.services.register(
      NPConfigurationServiceType.class, this.configuration);
    this.services.register(
      NPStrings.class, this.strings);
    this.services.register(
      NPTelemetryServiceType.class, this.telemetry);
    this.services.register(
      NPEventServiceType.class, this.events);
    this.services.register(
      NPMetricsServiceType.class, this.metrics);
    this.services.register(
      NPSCMRepositoryFactoryType.class, new NPSCMRepositoriesJGit()
    );
    this.services.register(
      NPDatabaseType.class, this.database
    );

    Mockito.when(this.configuration.configuration())
      .thenReturn(
        new NPServerConfiguration(
          Locale.ROOT,
          Clock.systemUTC(),
          this.strings,
          new NPPGDatabases(),
          DATABASE_FIXTURE.configuration(),
          new NPServerDirectoryConfiguration(
            reposDirectory,
            archiveDirectory
          ),
          new NPServerIdstoreConfiguration(
            URI.create("http://example.com:30000/"),
            URI.create("http://example.com:30000/")
          ),
          new NPServerAgentConfiguration(
            InetAddress.getLocalHost(),
            40000,
            TLS_DISABLED,
            1_000_000
          ),
          new NPServerArchiveConfiguration(
            InetAddress.getLocalHost(),
            40001,
            TLS_DISABLED,
            URI.create("https://archives.example.com/")
          ),
          new NPServerUserConfiguration(
            InetAddress.getLocalHost(),
            40002,
            TLS_DISABLED,
            1_000_000
          ),
          new NPServerMaintenanceConfiguration(
            Optional.empty(),
            Duration.ofDays(1L),
            Duration.ofDays(1L),
            Duration.ofDays(1L),
            Duration.ofDays(1L)
          ),
          Optional.empty()
        )
      );

    this.service =
      NPRepositoryService.create(this.services);
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.service.close();
  }

  /**
   * If there are no configured repositories, nothing happens.
   *
   * @throws Exception On errors
   */

  @Test
  public void testNoRepositories()
    throws Exception
  {
    this.service.start().get(1L, TimeUnit.SECONDS);
    this.service.check().get(1L, TimeUnit.SECONDS);
  }

  /**
   * A single repository works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testOneSampleRepository(
    final @TempDir Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("example.git.tar", reposDirectory);

    this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class)
      .execute(new NPSCMProviderDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        "SCM",
        URI.create("http://www.example.com")
      ));

    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        reposSource,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      ));

    this.transaction.commit();

    this.service.start().get(1L, TimeUnit.SECONDS);
    this.service.check().get(10L, TimeUnit.SECONDS);

    final var eventQueue = this.events.eventQueue();

    assertInstanceOf(NPRepositoryServiceStarted.class, eventQueue.poll());
    assertInstanceOf(NPRepositoryConfigured.class, eventQueue.poll());

    {
      final var e =
        assertInstanceOf(NPRepositoryUpdated.class, eventQueue.poll());
      assertEquals(13L, e.commits());
    }
  }

  /**
   * A failing repository fails checks.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailingRepository(
    final @TempDir Path reposDirectory)
    throws Exception
  {
    this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class)
      .execute(new NPSCMProviderDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        "SCM",
        URI.create("http://www.example.com")
      ));

    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        reposDirectory.toUri(),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      ));

    this.transaction.commit();

    this.service.start().get(1L, TimeUnit.SECONDS);
    this.service.check().get(10L, TimeUnit.SECONDS);

    final var eventQueue = this.events.eventQueue();

    assertInstanceOf(NPRepositoryServiceStarted.class, eventQueue.poll());
    assertInstanceOf(NPRepositoryConfigured.class, eventQueue.poll());
    assertInstanceOf(NPRepositoryUpdateFailed.class, eventQueue.poll());
  }

  /**
   * Unsupported repository providers fail.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailRepositoryProviderUnsupported(
    final @TempDir Path reposDirectory)
    throws Exception
  {
    this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class)
      .execute(new NPSCMProviderDescription(
        new RDottedName("com.io7m.unsupported"),
        "SCM",
        URI.create("http://www.example.com")
      ));

    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(new NPRepositoryDescription(
        new RDottedName("com.io7m.unsupported"),
        new NPRepositoryID(randomUUID()),
        reposDirectory.toUri(),
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      ));

    this.transaction.commit();

    this.service.start().get(1L, TimeUnit.SECONDS);
    this.service.check().get(10L, TimeUnit.SECONDS);

    final var eventQueue = this.events.eventQueue();

    assertInstanceOf(NPRepositoryServiceStarted.class, eventQueue.poll());
    assertInstanceOf(NPRepositoryConfigureFailed.class, eventQueue.poll());
  }

  /**
   * Creating an archive of a commit works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testArchiveCommit(
    final @TempDir Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("example.git.tar", reposDirectory);

    this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class)
      .execute(new NPSCMProviderDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        "SCM",
        URI.create("http://www.example.com")
      ));

    final var repositoryDescription =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        reposSource,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(repositoryDescription);

    this.transaction.commit();

    this.service.start().get(1L, TimeUnit.SECONDS);

    final var commit =
      new NPCommitID(
        repositoryDescription.id(),
        new NPCommitUnqualifiedID("11e4ee346c9a8708688acc4f32beac8955714b6c")
      );

    final var archive =
      this.service.createArchiveFor(commit)
        .get(10L, TimeUnit.SECONDS);

    assertEquals(commit, archive.commit());

    final var eventQueue = this.events.eventQueue();

    assertInstanceOf(NPRepositoryServiceStarted.class, eventQueue.poll());
    assertInstanceOf(NPRepositoryConfigured.class, eventQueue.poll());

    {
      final var e =
        assertInstanceOf(NPRepositoryUpdated.class, eventQueue.poll());
      assertEquals(13L, e.commits());
    }

    assertInstanceOf(NPRepositoryArchiveCreated.class, eventQueue.poll());
  }

  /**
   * Creating an archive of a nonexistent commit works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testArchiveCommitNonexistent(
    final @TempDir Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("example.git.tar", reposDirectory);

    this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class)
      .execute(new NPSCMProviderDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        "SCM",
        URI.create("http://www.example.com")
      ));

    final var repositoryDescription =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        reposSource,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(repositoryDescription);

    this.transaction.commit();

    this.service.start().get(1L, TimeUnit.SECONDS);

    final var commit =
      new NPCommitID(
        repositoryDescription.id(),
        new NPCommitUnqualifiedID("a5830879c9a5536e811df8ac4710d19e712a1232")
      );

    assertThrows(Exception.class, () -> {
      this.service.createArchiveFor(commit)
        .get(10L, TimeUnit.SECONDS);
    });
  }

  /**
   * Creating an archive of a nonexistent repository works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testArchiveCommitNonexistentRepository(
    final @TempDir Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("example.git.tar", reposDirectory);

    this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class)
      .execute(new NPSCMProviderDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        "SCM",
        URI.create("http://www.example.com")
      ));

    final var repositoryDescription =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        reposSource,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(repositoryDescription);

    this.transaction.commit();

    this.service.start().get(1L, TimeUnit.SECONDS);

    final var commit =
      new NPCommitID(
        new NPRepositoryID(randomUUID()),
        new NPCommitUnqualifiedID("11e4ee346c9a8708688acc4f32beac8955714b6c")
      );

    assertThrows(Exception.class, () -> {
      this.service.createArchiveFor(commit)
        .get(10L, TimeUnit.SECONDS);
    });
  }
}
