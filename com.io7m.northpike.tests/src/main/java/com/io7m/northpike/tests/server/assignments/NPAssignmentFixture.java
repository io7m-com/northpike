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

import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.clock.NPClock;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryCommitsGetMostRecentlyReceivedType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryCommitsPutType;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPHash;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPRepositorySigningPolicy;
import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.plans.NPPlanType;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanParsers;
import com.io7m.northpike.plans.parsers.NPPlanSerializers;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryType;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.archives.NPArchiveServiceType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventService;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPEventType;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.tests.NPEventInterceptingService;
import com.io7m.northpike.tests.containers.NPDatabaseFixture;
import com.io7m.northpike.tests.containers.NPIdstoreFixture;
import com.io7m.northpike.toolexec.api.NPTEvaluationService;
import com.io7m.northpike.toolexec.api.NPTEvaluationServiceType;
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
import java.util.Set;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS;
import static com.io7m.northpike.model.security.NPSecRole.LOGIN;
import static com.io7m.northpike.tests.scm_repository.NPSCMRepositoriesJGitTest.unpack;
import static java.util.UUID.randomUUID;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.when;

public final class NPAssignmentFixture implements AutoCloseable
{
  private final NPIdstoreFixture idstoreFixture;
  private final NPDatabaseFixture dbFixture;
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
    final NPIdstoreFixture inIdstoreFixture,
    final NPDatabaseFixture inDbFixture,
    final NPSCMRepositoryType inRepositoryUnsigned,
    final NPSCMRepositoryType inRepositoryRequireSigned,
    final NPSCMRepositoryType inRepositoryRequireSignedSpecific)
  {
    this.idstoreFixture =
      Objects.requireNonNull(inIdstoreFixture, "idstoreFixture");
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
    final NPIdstoreFixture idstoreFixture,
    final NPDatabaseFixture databaseFixture,
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
        new NPRepositoryID(randomUUID()),
        reposSourceUnsigned,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    final var repositoryDescriptionRequireSigned =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        reposSourceSigned,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY
      );

    final var repositoryDescriptionRequireSignedSpecific =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
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
      idstoreFixture,
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
      new NPAuditOwnerType.User(this.idstoreFixture.userWithLoginId())
    );
    this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class)
      .execute(new NPUser(
        this.idstoreFixture.userWithLoginId(),
        this.idstoreFixture.userWithLoginName(),
        new MSubject(Set.of(LOGIN.role()))
      ));
    this.transaction.commit();

    final var strings =
      NPStrings.create(Locale.ROOT);

    this.services.register(
      NPTelemetryServiceType.class, NPTelemetryNoOp.noop());
    this.services.register(
      NPStrings.class, strings);
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
      NPTEvaluationServiceType.class,
      NPTEvaluationService.createFromServiceLoader(strings)
    );

    this.createRepositories();
    this.transaction.commit();

    Mockito.when(this.mockRepositoryService.commitCreateArchiveFor(any()))
      .thenReturn(new NPArchive(
        NPToken.generate(),
        this.commitHeadUnsigned.id(),
        new NPHash(
          "SHA-256",
          "a939645e193074c683dd7132c65a5571e8fdb59d67cbe1c17ff7c29b5289647c"
        ),
        OffsetDateTime.now()
      ));

    Mockito.when(
      this.mockRepositoryService.commitGet(this.commitUnsigned()))
      .thenReturn(this.commitUnsignedValue());
    Mockito.when(
      this.mockRepositoryService.commitGet(this.commitSigned()))
      .thenReturn(this.commitSignedValue());
    Mockito.when(
      this.mockRepositoryService.commitGet(this.commitSignedSpecific()))
      .thenReturn(this.commitSignedSpecificValue());
  }

  private void createRepositories()
    throws Exception
  {
    this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class)
      .execute(this.repositoryRequireSignedSpecific.description());
    this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class)
      .execute(this.repositoryRequireSigned.description());
    this.transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryPutType.class)
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
      this.transaction.queries(RepositoryCommitsGetMostRecentlyReceivedType.class)
        .execute(this.repositoryRequireSignedSpecific.description().id())
        .map(NPCommitSummary::timeReceived);

    final var commits =
      this.repositoryRequireSignedSpecific.commitsSinceTime(since);

    this.commitHeadSignedSpecific =
      commits.commits()
        .stream()
        .max(Comparator.comparing(NPCommit::timeCreated))
        .orElseThrow();

    this.transaction.queries(RepositoryCommitsPutType.class)
      .execute(new RepositoryCommitsPutType.Parameters(
        commits.commits(),
        commits.commitGraph()
      ));
  }

  private void setupReposSigned()
    throws Exception
  {
    final var since =
      this.transaction.queries(RepositoryCommitsGetMostRecentlyReceivedType.class)
        .execute(this.repositoryRequireSigned.description().id())
        .map(NPCommitSummary::timeReceived);

    final var commits =
      this.repositoryRequireSigned.commitsSinceTime(since);

    this.commitHeadSigned =
      commits.commits()
        .stream()
        .max(Comparator.comparing(NPCommit::timeCreated))
        .orElseThrow();

    this.transaction.queries(RepositoryCommitsPutType.class)
      .execute(new RepositoryCommitsPutType.Parameters(
        commits.commits(),
        commits.commitGraph()
      ));
  }

  private void setupReposUnsigned()
    throws Exception
  {
    final var since =
      this.transaction.queries(RepositoryCommitsGetMostRecentlyReceivedType.class)
        .execute(this.repositoryUnsigned.description().id())
        .map(NPCommitSummary::timeReceived);

    final var commits =
      this.repositoryUnsigned.commitsSinceTime(since);

    this.commitHeadUnsigned =
      commits.commits()
        .stream()
        .max(Comparator.comparing(NPCommit::timeCreated))
        .orElseThrow();

    this.transaction.queries(RepositoryCommitsPutType.class)
      .execute(new RepositoryCommitsPutType.Parameters(
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
    this.transaction.queries(NPDatabaseQueriesPlansType.PlanPutType.class)
      .execute(new NPDatabaseQueriesPlansType.PlanPutType.Parameters(
        plan,
        new NPPlanSerializers()
      ));

    final var assignment =
      switch (signingPolicy) {
        case REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY -> {
          yield new NPAssignment(
            NPAssignmentName.of("com.io7m.a1"),
            this.repositoryRequireSigned.description().id(),
            plan.identifier(),
            NPAssignmentScheduleNone.SCHEDULE_NONE
          );
        }
        case ALLOW_UNSIGNED_COMMITS -> {
          yield new NPAssignment(
            NPAssignmentName.of("com.io7m.a1"),
            this.repositoryUnsigned.description().id(),
            plan.identifier(),
            NPAssignmentScheduleNone.SCHEDULE_NONE
          );
        }
        case REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS -> {
          yield new NPAssignment(
            NPAssignmentName.of("com.io7m.a1"),
            this.repositoryRequireSignedSpecific.description().id(),
            plan.identifier(),
            NPAssignmentScheduleNone.SCHEDULE_NONE
          );
        }
      };

    this.transaction.queries(NPDatabaseQueriesAssignmentsType.AssignmentPutType.class)
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

  public NPCommit commitUnsignedValue()
  {
    return new NPCommit(
      this.commitUnsigned(),
      OffsetDateTime.now(),
      OffsetDateTime.now(),
      new NPCommitAuthor("Someone", "someone@example.com"),
      "Unsigned",
      "Body",
      Set.of(),
      Set.of()
    );
  }

  public Queue<NPEventType> events()
  {
    return this.events.eventQueue();
  }

  public NPCommitID commitSigned()
  {
    return this.commitHeadSigned.id();
  }

  public NPCommit commitSignedValue()
  {
    return new NPCommit(
      this.commitSigned(),
      OffsetDateTime.now(),
      OffsetDateTime.now(),
      new NPCommitAuthor("Someone", "someone@example.com"),
      "Signed",
      "Body",
      Set.of(),
      Set.of()
    );
  }

  public NPCommitID commitSignedSpecific()
  {
    return this.commitHeadSignedSpecific.id();
  }

  public NPCommit commitSignedSpecificValue()
  {
    return new NPCommit(
      this.commitSignedSpecific(),
      OffsetDateTime.now(),
      OffsetDateTime.now(),
      new NPCommitAuthor("Someone", "someone@example.com"),
      "Signed with specific key",
      "Body",
      Set.of(),
      Set.of()
    );
  }

  public void setRepositorySigningPolicy(
    final NPRepositorySigningPolicy policy)
    throws InterruptedException, NPException
  {
    when(this.mockRepositoryService().repositorySigningPolicyFor(any()))
      .thenReturn(policy);
  }
}
