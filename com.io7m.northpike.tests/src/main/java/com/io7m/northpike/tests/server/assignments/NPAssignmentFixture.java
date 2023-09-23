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


package com.io7m.northpike.tests.server.assignments;

import com.io7m.northpike.assignments.NPAssignment;
import com.io7m.northpike.assignments.NPAssignmentName;
import com.io7m.northpike.clock.NPClock;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.CommitsGetMostRecentlyReceivedType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.CommitsPutType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPHash;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositorySigningPolicy;
import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.plans.NPPlanType;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanParsers;
import com.io7m.northpike.plans.parsers.NPPlanSerializers;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryType;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.archives.NPArchiveServiceType;
import com.io7m.northpike.server.internal.events.NPEventService;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.server.internal.telemetry.NPTelemetryNoOp;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPEventType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.tests.NPEventInterceptingService;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.northpike.toolexec.NPTXParserFactoryType;
import com.io7m.northpike.toolexec.NPTXParsers;
import com.io7m.repetoir.core.RPServiceDirectory;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import org.mockito.Mockito;

import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Clock;
import java.time.OffsetDateTime;
import java.util.Comparator;
import java.util.Locale;
import java.util.Objects;
import java.util.Queue;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS;
import static com.io7m.northpike.tests.scm_repository.NPSCMRepositoriesJGitTest.unpack;
import static org.mockito.ArgumentMatchers.any;

public final class NPAssignmentFixture implements AutoCloseable
{
  private final NPTestContainers.NPDatabaseFixture dbFixture;
  private final NPSCMRepositoryType repositoryUnsigned;
  private final NPSCMRepositoryType repositoryRequireSigned;
  private final NPSCMRepositoryType repositoryRequireSignedSpecific;
  private NPCommit commitHeadUnsigned;
  private RPServiceDirectory services;
  private NPDatabaseType database;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPEventInterceptingService events;
  private NPAgentServiceType mockAgentService;
  private NPArchiveServiceType mockArchiveService;
  private NPCommit commitHeadSigned;
  private NPCommit commitHeadSignedSpecific;
  private NPRepositoryServiceType mockRepositoryService;

  private NPAssignmentFixture(
    final NPTestContainers.NPDatabaseFixture inDbFixture,
    final NPSCMRepositoryType inRepositoryUnsigned,
    final NPSCMRepositoryType inRepositoryRequireSigned,
    final NPSCMRepositoryType inRepositoryRequireSignedSpecific)
  {
    this.dbFixture =
      Objects.requireNonNull(inDbFixture, "fixture");
    this.repositoryUnsigned =
      Objects.requireNonNull(inRepositoryUnsigned, "repository");
    this.repositoryRequireSigned =
      Objects.requireNonNull(
        inRepositoryRequireSigned,
        "repositoryRequireSigned");
    this.repositoryRequireSignedSpecific =
      Objects.requireNonNull(
        inRepositoryRequireSignedSpecific,
        "repositoryRequireSignedSpecific");
  }

  public static NPAssignmentFixture create(
    final NPTestContainers.NPDatabaseFixture databaseFixture,
    final Path reposDirectory)
    throws Exception
  {
    final var reposDirectoryUnsigned =
      reposDirectory.resolve("unsigned");
    final var reposDirectorySigned =
      reposDirectory.resolve("signed");
    final var reposDirectorySignedSpecific =
      reposDirectory.resolve("signedSpecific");

    Files.createDirectories(reposDirectorySigned);
    Files.createDirectories(reposDirectorySignedSpecific);
    Files.createDirectories(reposDirectoryUnsigned);

    final var reposSourceUnsigned =
      unpack("example.git.tar", reposDirectoryUnsigned);
    final var reposSourceSigned =
      unpack("example.git.tar", reposDirectorySigned);
    final var reposSourceSignedSpecific =
      unpack("example.git.tar", reposDirectorySignedSpecific);

    final var repositoryProvider =
      new NPSCMRepositoriesJGit();

    final var repositoryDescriptionUnsigned =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        UUID.randomUUID(),
        reposSourceUnsigned,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    final var repositoryDescriptionRequireSigned =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        UUID.randomUUID(),
        reposSourceSigned,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY
      );

    final var repositoryDescriptionRequireSignedSpecific =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        UUID.randomUUID(),
        reposSourceSignedSpecific,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS
      );

    final var tmpServices =
      new RPServiceDirectory();
    tmpServices.register(
      NPStrings.class, NPStrings.create(Locale.ROOT));
    tmpServices.register(
      NPTelemetryServiceType.class, NPTelemetryNoOp.noop());
    tmpServices.register(
      NPClockServiceType.class, new NPClock(Clock.systemUTC()));

    final var repositoryUnsigned =
      repositoryProvider.createRepository(
        tmpServices,
        reposDirectory,
        repositoryDescriptionUnsigned
      );

    final var repositoryRequireSigned =
      repositoryProvider.createRepository(
        tmpServices,
        reposDirectory,
        repositoryDescriptionRequireSigned
      );

    final var repositoryRequireSignedSpecific =
      repositoryProvider.createRepository(
        tmpServices,
        reposDirectory,
        repositoryDescriptionRequireSignedSpecific
      );

    return new NPAssignmentFixture(
      databaseFixture,
      repositoryUnsigned,
      repositoryRequireSigned,
      repositoryRequireSignedSpecific
    );
  }

  public NPDatabaseType database()
  {
    return this.database;
  }

  public NPDatabaseConnectionType connection()
  {
    return this.connection;
  }

  public NPDatabaseTransactionType transaction()
  {
    return this.transaction;
  }

  public NPEventInterceptingService eventService()
  {
    return this.events;
  }

  public void reset(
    final CloseableResourcesType closeables)
    throws Exception
  {
    this.dbFixture.reset();

    if (this.services != null) {
      this.services.close();
    }
    this.services = new RPServiceDirectory();

    final var clock =
      new NPClock(Clock.systemUTC());
    this.events =
      new NPEventInterceptingService(
        NPEventService.create(NPTelemetryNoOp.noop())
      );
    this.mockAgentService =
      Mockito.mock(NPAgentServiceType.class);
    this.mockArchiveService =
      Mockito.mock(NPArchiveServiceType.class);
    this.mockRepositoryService =
      Mockito.mock(NPRepositoryServiceType.class);

    this.database =
      closeables.addPerTestResource(this.dbFixture.createDatabase());
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

    this.services.register(
      NPTelemetryServiceType.class, NPTelemetryNoOp.noop());
    this.services.register(
      NPStrings.class, NPStrings.create(Locale.ROOT));
    this.services.register(
      NPDatabaseType.class, this.database);
    this.services.register(
      NPClockServiceType.class, clock);
    this.services.register(
      NPEventServiceType.class, this.events);
    this.services.register(
      NPAgentServiceType.class, this.mockAgentService);
    this.services.register(
      NPArchiveServiceType.class, this.mockArchiveService);
    this.services.register(
      NPRepositoryServiceType.class, this.mockRepositoryService);
    this.services.register(
      NPPlanParserFactoryType.class, new NPPlanParsers());
    this.services.register(
      NPTXParserFactoryType.class, new NPTXParsers());

    this.createRepositories();
    this.transaction.commit();

    Mockito.when(this.mockRepositoryService.createArchiveFor(any()))
      .thenReturn(CompletableFuture.completedFuture(
        new NPArchive(
          NPToken.generate(),
          this.commitHeadUnsigned.id(),
          new NPHash(
            "SHA-256",
            "a939645e193074c683dd7132c65a5571e8fdb59d67cbe1c17ff7c29b5289647c"
          ),
          OffsetDateTime.now()
        )
      ));
  }

  private void createRepositories()
    throws Exception
  {
    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(this.repositoryRequireSignedSpecific.description());
    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(this.repositoryRequireSigned.description());
    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(this.repositoryUnsigned.description());
    this.transaction.commit();

    this.setupReposUnsigned();
    this.setupReposSigned();
    this.setupReposSignedSpecific();
    this.transaction.commit();
  }

  private void setupReposSignedSpecific()
    throws Exception
  {
    final var since =
      this.transaction.queries(CommitsGetMostRecentlyReceivedType.class)
        .execute(this.repositoryRequireSignedSpecific.description().id())
        .map(NPCommitSummary::timeReceived);

    final var commits =
      this.repositoryRequireSignedSpecific.commitsSinceTime(since);

    this.commitHeadSignedSpecific =
      commits.commits()
        .stream()
        .max(Comparator.comparing(NPCommit::timeCreated))
        .orElseThrow();

    this.transaction.queries(CommitsPutType.class)
      .execute(new CommitsPutType.Parameters(
        commits.commits(),
        commits.commitGraph()
      ));
  }

  private void setupReposSigned()
    throws Exception
  {
    final var since =
      this.transaction.queries(CommitsGetMostRecentlyReceivedType.class)
        .execute(this.repositoryRequireSigned.description().id())
        .map(NPCommitSummary::timeReceived);

    final var commits =
      this.repositoryRequireSigned.commitsSinceTime(since);

    this.commitHeadSigned =
      commits.commits()
        .stream()
        .max(Comparator.comparing(NPCommit::timeCreated))
        .orElseThrow();

    this.transaction.queries(CommitsPutType.class)
      .execute(new CommitsPutType.Parameters(
        commits.commits(),
        commits.commitGraph()
      ));
  }

  private void setupReposUnsigned()
    throws Exception
  {
    final var since =
      this.transaction.queries(CommitsGetMostRecentlyReceivedType.class)
        .execute(this.repositoryUnsigned.description().id())
        .map(NPCommitSummary::timeReceived);

    final var commits =
      this.repositoryUnsigned.commitsSinceTime(since);

    this.commitHeadUnsigned =
      commits.commits()
        .stream()
        .max(Comparator.comparing(NPCommit::timeCreated))
        .orElseThrow();

    this.transaction.queries(CommitsPutType.class)
      .execute(new CommitsPutType.Parameters(
        commits.commits(),
        commits.commitGraph()
      ));
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.services != null) {
      this.services.close();
    }
  }

  public NPRepositoryServiceType mockRepositoryService()
  {
    return this.mockRepositoryService;
  }

  public NPArchiveServiceType mockArchiveService()
  {
    return this.mockArchiveService;
  }

  public NPAgentServiceType mockAgentService()
  {
    return this.mockAgentService;
  }

  public NPAssignment createAssignmentWithPlan(
    final NPRepositorySigningPolicy signingPolicy,
    final NPPlanType plan)
    throws Exception
  {
    this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class)
      .execute(new NPDatabaseQueriesPlansType.PutType.Parameters(
        plan,
        new NPPlanSerializers()
      ));

    final var assignment =
      switch (signingPolicy) {
        case REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY -> {
          yield new NPAssignment(
            NPAssignmentName.of("com.io7m.a1"),
            this.repositoryRequireSigned.description().id(),
            plan.identifier()
          );
        }
        case ALLOW_UNSIGNED_COMMITS -> {
          yield new NPAssignment(
            NPAssignmentName.of("com.io7m.a1"),
            this.repositoryUnsigned.description().id(),
            plan.identifier()
          );
        }
        case REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS -> {
          yield new NPAssignment(
            NPAssignmentName.of("com.io7m.a1"),
            this.repositoryRequireSignedSpecific.description().id(),
            plan.identifier()
          );
        }
      };

    this.transaction.queries(NPDatabaseQueriesAssignmentsType.PutType.class)
      .execute(assignment);

    this.transaction.commit();
    return assignment;
  }

  public RPServiceDirectoryType services()
  {
    return this.services;
  }

  public NPCommitID commitUnsigned()
  {
    return this.commitHeadUnsigned.id();
  }

  public Queue<NPEventType> events()
  {
    return this.events.eventQueue();
  }

  public NPCommitID commitSigned()
  {
    return this.commitHeadSigned.id();
  }

  public NPCommitID commitSignedSpecific()
  {
    return this.commitHeadSignedSpecific.id();
  }
}
