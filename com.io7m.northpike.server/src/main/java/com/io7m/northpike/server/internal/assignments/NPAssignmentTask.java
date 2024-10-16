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


package com.io7m.northpike.server.internal.assignments;

import com.io7m.jmulticlose.core.CloseableType;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentGetType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentExecutionPutType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentWorkItemPutType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.PlanGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPublicKeysType.PublicKeyGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.GetExecutionDescriptionType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPArchiveWithLinks;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPRepositorySigningPolicy;
import com.io7m.northpike.model.NPToolExecutionEvaluated;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.NPWorkItemStatus;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentExecution;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreated;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreatedType;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreationFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRequested;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRunning;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateSucceeded;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.model.plans.NPPlanBarrierType;
import com.io7m.northpike.model.plans.NPPlanElementName;
import com.io7m.northpike.model.plans.NPPlanElementType;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanTaskType;
import com.io7m.northpike.model.plans.NPPlanType;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluation;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.ElementBecameReady;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.ElementFailed;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.ElementSucceeded;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskAgentSelectionTimedOut;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskExecutionTimedOut;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskRequiresMatchingAgent;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskRequiresSpecificAgent;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusFailed;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusInProgress;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusSucceeded;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentAcceptedTask;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentReportedTaskFailure;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentReportedTaskSuccess;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.preparation.NPPlanPreparation;
import com.io7m.northpike.plans.preparation.NPPlanPreparationType;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemAccepted;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemEventType;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemStatusChanged;
import com.io7m.northpike.server.internal.archives.NPArchiveServiceType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPEventType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.toolexec.api.NPTEvaluationResult;
import com.io7m.northpike.toolexec.api.NPTEvaluationServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.Flow.Subscriber;
import java.util.concurrent.Flow.Subscription;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE_READ_ONLY;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorSignatureVerificationFailed;
import static com.io7m.northpike.server.internal.assignments.NPAssignmentLogging.recordErrorText;
import static com.io7m.northpike.server.internal.assignments.NPAssignmentLogging.recordInfoText;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_ID;
import static com.io7m.northpike.strings.NPStringConstants.ASSIGNMENT;
import static com.io7m.northpike.strings.NPStringConstants.COMMIT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_KEY_NOT_ASSIGNED;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;
import static com.io7m.northpike.strings.NPStringConstants.KEY;
import static com.io7m.northpike.strings.NPStringConstants.PLAN;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_VERSION;
import static com.io7m.northpike.strings.NPStringConstants.REPOSITORY;
import static com.io7m.northpike.strings.NPStringConstants.TASK;
import static com.io7m.northpike.strings.NPStringConstants.TOOL_REFERENCE;
import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;

/**
 * A task controlling the full execution of a single assignment.
 */

public final class NPAssignmentTask
  implements Runnable, CloseableType, Subscriber<NPEventType>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAssignmentTask.class);

  private final AtomicLong eventIndex;
  private final AtomicBoolean closed;
  private final ConcurrentLinkedQueue<NPPlanEvaluationUpdateType> planUpdates;
  private final NPAgentServiceType agents;
  private final NPArchiveServiceType archives;
  private final NPAssignmentExecutionRequest assignmentRequest;
  private final NPClockServiceType clock;
  private final NPDatabaseType database;
  private final NPEventServiceType events;
  private final NPRepositoryServiceType repositories;
  private final NPStrings strings;
  private final NPTelemetryServiceType telemetry;
  private final Set<NPPlanParserFactoryType> planParsers;
  private final NPTEvaluationServiceType toolExecEvaluation;
  private final NPAssignmentExecutionID executionId;
  private final Map<String, String> logAttributes;

  private NPArchive archive;
  private NPAssignment assignment;
  private NPAssignmentExecution assignmentExecution;
  private NPAssignmentExecutionStateType executionState;
  private NPCommit commit;
  private NPPlanEvaluationType planEvaluator;
  private NPPlanPreparationType planPreparation;
  private NPPlanType plan;
  private OffsetDateTime timeCreated;
  private OffsetDateTime timeEnded;
  private OffsetDateTime timeStarted;
  private NPArchiveLinks archiveLinks;

  private NPAssignmentTask(
    final NPDatabaseType inDatabase,
    final NPClockServiceType inClock,
    final NPEventServiceType inEvents,
    final NPTelemetryServiceType inTelemetry,
    final NPAgentServiceType inAgents,
    final NPRepositoryServiceType inRepositories,
    final NPArchiveServiceType inArchives,
    final Set<NPPlanParserFactoryType> inParserFactories,
    final NPTEvaluationServiceType inToolExecEvaluation,
    final NPStrings inStrings,
    final NPAssignmentExecutionRequest inRequest,
    final NPAssignmentExecutionID inExecutionId)
  {
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.clock =
      Objects.requireNonNull(inClock, "clock");
    this.events =
      Objects.requireNonNull(inEvents, "inEvents");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "inTelemetry");
    this.agents =
      Objects.requireNonNull(inAgents, "agents");
    this.repositories =
      Objects.requireNonNull(inRepositories, "repositories");
    this.archives =
      Objects.requireNonNull(inArchives, "inArchives");
    this.planParsers =
      Objects.requireNonNull(inParserFactories, "parserFactories");
    this.toolExecEvaluation =
      Objects.requireNonNull(inToolExecEvaluation, "toolExecEvaluation");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.assignmentRequest =
      Objects.requireNonNull(inRequest, "request");
    this.executionId =
      Objects.requireNonNull(inExecutionId, "inExecutionId");

    this.logAttributes =
      new HashMap<>();
    this.eventIndex =
      new AtomicLong(Long.MIN_VALUE);

    this.executionState =
      new NPAssignmentExecutionStateRequested(
        this.executionId,
        this.assignmentRequest,
        this.timeCalculateCreated()
      );

    this.closed =
      new AtomicBoolean(false);
    this.planUpdates =
      new ConcurrentLinkedQueue<>();
    this.events.events()
      .subscribe(this);
  }

  /**
   * Create a new assignment task.
   *
   * @param services    The service directory
   * @param assignment  The assignment
   * @param executionId An execution ID
   *
   * @return A new assignment task
   */

  public static NPAssignmentTask create(
    final RPServiceDirectoryType services,
    final NPAssignmentExecutionRequest assignment,
    final NPAssignmentExecutionID executionId)
  {
    return new NPAssignmentTask(
      services.requireService(NPDatabaseType.class),
      services.requireService(NPClockServiceType.class),
      services.requireService(NPEventServiceType.class),
      services.requireService(NPTelemetryServiceType.class),
      services.requireService(NPAgentServiceType.class),
      services.requireService(NPRepositoryServiceType.class),
      services.requireService(NPArchiveServiceType.class),
      Set.copyOf(services.optionalServices(NPPlanParserFactoryType.class)),
      services.requireService(NPTEvaluationServiceType.class),
      services.requireService(NPStrings.class),
      assignment,
      executionId
    );
  }

  private static void pauseQuietly()
  {
    try {
      Thread.sleep(1_000L);
    } catch (final InterruptedException e) {
      Thread.currentThread().interrupt();
    }
  }

  @Override
  public void run()
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("AssignmentTaskExecution")
        .setAttribute("AssignmentExecutionID", this.executionId.toString())
        .setAttribute(
          "Assignment",
          this.assignmentRequest.assignment().toString())
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      try {
        this.assignmentCreateInitialState();
        this.assignmentCreateExecution();
        this.assignmentCheckAllowed();
        this.assignmentCreateArchive();
        this.assignmentCompilePlan();
        this.assignmentStart();
        this.assignmentRun();
      } catch (final Exception e) {
        LOG.error("Assignment failed: ", e);
        recordSpanException(e);
        this.assignmentFailed();
        throw e;
      }
    } catch (final Throwable e) {
      recordSpanException(e);
      this.recordExceptionText(e);
    } finally {
      span.end();
    }
  }

  private void assignmentCheckAllowed()
    throws InterruptedException, NPException
  {
    this.logInfo("Checking commit signature against signing policy.");

    switch (this.assignmentGetSigningPolicy()) {

      /*
       * Commits are allowed to be unsigned. This is morally equivalent to not
       * checking commit signatures at all.
       */

      case ALLOW_UNSIGNED_COMMITS -> {
        this.logAttributes.clear();
        this.logInfo("Unsigned commits are allowed; ignoring signature.");
      }

      /*
       * Commits are required to be signed with keys that we know about.
       */

      case REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY -> {
        this.logInfo(
          "Commit must be signed with a known key; verifying signature.");

        try {
          final var fingerprint =
            this.repositories.commitSignatureVerify(
              this.commit.id(),
              this::findKey
            );

          this.logAttributes.clear();
          this.logAttributes.put("Key", fingerprint.value());
          this.logInfo("Commit has valid signature from key %s.", fingerprint);
        } catch (final Exception e) {
          this.assignmentFailed();
          throw e;
        }
      }

      /*
       * Commits are required to be signed with keys that are assigned to
       * the repository.
       */

      case REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS -> {
        this.logInfo(
          "Commit must be signed with a specific key; verifying signature.");

        try {
          final var fingerprint =
            this.repositories.commitSignatureVerify(
              this.commit.id(),
              this::findKey
            );

          final var isKeyAssigned =
            this.keyIsAssignedToCurrentRepository(fingerprint);

          if (!isKeyAssigned) {
            throw this.errorKeyNotAssignedToRepository(fingerprint);
          }

          this.logAttributes.clear();
          this.logAttributes.put("Key", fingerprint.value());
          this.logInfo("Commit has valid signature from key %s.", fingerprint);
        } catch (final Exception e) {
          this.assignmentFailed();
          throw e;
        }
      }
    }
  }

  private NPPublicKey findKey(
    final NPFingerprint fingerprint)
    throws NPException
  {
    try (var connection = this.database.openConnection(NORTHPIKE_READ_ONLY);
         var transaction = connection.openTransaction()) {
      return transaction.queries(PublicKeyGetType.class)
        .execute(fingerprint)
        .orElseThrow(() -> this.errorNonexistentPublicKey(fingerprint));
    }
  }

  private NPServerException errorNonexistentPublicKey(
    final NPFingerprint fingerprint)
  {
    return new NPServerException(
      this.strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(KEY),
          fingerprint.value()
        )
      ),
      Optional.empty()
    );
  }

  private NPRepositorySigningPolicy assignmentGetSigningPolicy()
    throws NPException, InterruptedException
  {
    return this.repositories.repositorySigningPolicyFor(this.assignment.repositoryId());

  }

  private NPServerException errorKeyNotAssignedToRepository(
    final NPFingerprint fingerprint)
  {
    return new NPServerException(
      this.strings.format(ERROR_KEY_NOT_ASSIGNED),
      errorSignatureVerificationFailed(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(REPOSITORY),
          this.assignment.repositoryId().toString()
        ),
        Map.entry(
          this.strings.format(KEY),
          fingerprint.value()
        ),
        Map.entry(
          this.strings.format(COMMIT),
          this.commit.id().commitId().value()
        )
      ),
      Optional.empty()
    );
  }

  private boolean keyIsAssignedToCurrentRepository(
    final NPFingerprint fingerprint)
    throws NPException, InterruptedException
  {
    return this.repositories.repositoryHasPublicKeyAssigned(
      this.commit.id().repository(),
      fingerprint
    );
  }

  private void recordExceptionText(
    final Throwable e)
  {
    try (var connection = this.database.openConnection(NORTHPIKE);
         var transaction = connection.openTransaction()) {
      NPAssignmentLogging.recordException(
        transaction,
        this.executionId,
        this.eventIndexNext(),
        e
      );
      transaction.commit();
    } catch (final NPDatabaseException ex) {
      recordSpanException(ex);
    }
  }

  private void assignmentCompilePlan()
    throws NPException
  {
    try (var connection = this.database.openConnection(NORTHPIKE);
         var transaction = connection.openTransaction()) {

      final var planGet =
        transaction.queries(PlanGetType.class);
      final var toolGet =
        transaction.queries(GetExecutionDescriptionType.class);

      final var planOpt =
        planGet.execute(new PlanGetType.Parameters(
          this.assignment.plan(),
          this.planParsers
        ));

      if (planOpt.isEmpty()) {
        throw this.errorNonexistentPlan(this.assignment.plan());
      }

      this.plan =
        NPPlans.toPlan(planOpt.get(), this.strings);

      this.planEvaluator =
        NPPlanEvaluation.create(
          this.clock.clock(),
          this.plan
        );

      final var compiler =
        new NPAssignmentToolExecutionCompiler(
          this.strings,
          this.toolExecEvaluation,
          toolGet
        );

      this.archiveLinks =
        this.archives.linksForArchive(this.archive);

      this.planPreparation =
        NPPlanPreparation.forCommit(
          compiler,
          this.commit,
          new NPArchiveWithLinks(this.archive, this.archiveLinks),
          this.plan
        );

      this.setAssignmentExecutionState(
        transaction,
        new NPAssignmentExecutionStateCreated(
          this.timeCalculateCreated(),
          this.assignmentExecution
        )
      );

      this.createWorkItems(transaction);
      transaction.commit();
    }

    this.logAttributes.clear();
    this.logAttributes.put("Plan", this.plan.identifier().toString());
    this.logInfo("Compiled plan %s", this.plan.identifier().toString());
  }

  /**
   * Create the set of work items required for the plan.
   */

  private void createWorkItems(
    final NPDatabaseTransactionType transaction)
    throws NPDatabaseException
  {
    for (final var planElement : this.plan.elements().values()) {
      this.createWorkItemForPlanElement(transaction, planElement);
    }
  }

  private void createWorkItemForPlanElement(
    final NPDatabaseTransactionType transaction,
    final NPPlanElementType planElement)
    throws NPDatabaseException
  {
    switch (planElement) {
      case final NPPlanBarrierType ignored -> {
        // Barriers do not get recorded as work items.
      }
      case final NPPlanTaskType task -> {
        this.createWorkItemForTask(transaction, task);
      }
    }
  }

  private void createWorkItemForTask(
    final NPDatabaseTransactionType transaction,
    final NPPlanTaskType task)
    throws NPDatabaseException
  {
    final var workItemIdentifier =
      new NPWorkItemIdentifier(
        this.assignmentExecution.id(),
        task.name().name()
      );

    final var workItem =
      new NPWorkItem(
        workItemIdentifier,
        Optional.empty(),
        NPWorkItemStatus.WORK_ITEM_CREATED
      );

    transaction.queries(AssignmentWorkItemPutType.class)
      .execute(workItem);
  }

  private void logInfo(
    final String format,
    final Object... arguments)
  {
    final var formatted = format.formatted(arguments);
    LOG.info("{}", formatted);

    try (var connection = this.database.openConnection(NORTHPIKE);
         var transaction = connection.openTransaction()) {
      recordInfoText(
        transaction,
        this.executionId,
        Map.copyOf(this.logAttributes),
        this.eventIndexNext(),
        formatted
      );
      transaction.commit();
    } catch (final NPDatabaseException e) {
      recordSpanException(e);
    }
  }

  private void logError(
    final String format,
    final Object... arguments)
  {
    final var formatted = format.formatted(arguments);
    LOG.info("{}", formatted);

    try (var connection = this.database.openConnection(NORTHPIKE);
         var transaction = connection.openTransaction()) {
      recordErrorText(
        transaction,
        this.executionId,
        Map.copyOf(this.logAttributes),
        this.eventIndexNext(),
        formatted
      );
      transaction.commit();
    } catch (final NPDatabaseException e) {
      recordSpanException(e);
    }
  }

  private long eventIndexNext()
  {
    return this.eventIndex.getAndIncrement();
  }

  private NPServerException errorNonexistentPlan(
    final NPPlanIdentifier planId)
  {
    return new NPServerException(
      this.strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(PLAN),
          planId.name().toString()
        ),
        Map.entry(
          this.strings.format(PLAN_VERSION),
          Long.toUnsignedString(planId.version())
        )
      ),
      Optional.empty()
    );
  }

  private NPServerException errorSpecificAgentNonexistent(
    final NPAgentID agentID)
  {
    return new NPServerException(
      this.strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(AGENT_ID),
          agentID.toString()
        )
      ),
      Optional.empty()
    );
  }

  private void assignmentCreateArchive()
    throws Exception
  {
    try {
      this.archive = this.repositories.commitCreateArchiveFor(this.commit.id());
    } catch (final Exception e) {
      this.assignmentFailed();
      throw e;
    }
  }

  private void assignmentRun()
    throws NPException
  {
    final var updatesNow =
      new ArrayList<NPPlanEvaluationUpdateType>();

    while (!this.closed.get()) {
      updatesNow.clear();
      while (!this.planUpdates.isEmpty()) {
        updatesNow.add(this.planUpdates.poll());
      }

      final var planStatus =
        this.planEvaluator.step(List.copyOf(updatesNow));

      for (final var event : planStatus.events()) {
        this.onPlanEvent(event);
      }

      switch (planStatus) {
        case final StatusFailed f -> {
          this.assignmentFailed();
          return;
        }
        case final StatusSucceeded s -> {
          this.assignmentSucceeded();
          return;
        }
        case final StatusInProgress p -> {
          pauseQuietly();
        }
      }
    }
  }

  private void onPlanEvent(
    final NPPlanEvaluationEventType event)
    throws NPException
  {
    LOG.debug("Plan event: {}", event);

    switch (event) {
      case final ElementBecameReady e -> {
        this.logAttributes.clear();
        this.logAttributes.put("Element", e.element().name().toString());
        this.logInfo("Element became ready.");
        return;
      }

      case final ElementFailed e -> {
        this.logAttributes.clear();
        this.logAttributes.put("Element", e.element().name().toString());
        this.logError("Element failed.");
        return;
      }

      case final ElementSucceeded e -> {
        this.logAttributes.clear();
        this.logAttributes.put("Element", e.element().name().toString());
        this.logInfo("Element succeeded.");
        return;
      }

      case final TaskRequiresSpecificAgent specific -> {
        this.onPlanEventTaskRequiresSpecificAgent(specific);
        return;
      }

      case final TaskRequiresMatchingAgent matching -> {
        this.onPlanEventTaskRequiresMatchingAgent(matching.task());
        return;
      }

      case final TaskAgentSelectionTimedOut e -> {
        this.logAttributes.clear();
        this.logAttributes.put("Task", e.task().name().toString());
        this.logError("Task agent selection timed out.");
        return;
      }

      case final TaskExecutionTimedOut e -> {
        this.logAttributes.clear();
        this.logAttributes.put("Task", e.task().name().toString());
        this.logError("Task execution timed out.");
        return;
      }
    }
  }

  private void onPlanEventTaskRequiresSpecificAgent(
    final TaskRequiresSpecificAgent specific)
    throws NPServerException, NPDatabaseException
  {
    final var agentId =
      specific.agent();
    final var agentDescriptions =
      this.findAgents(Set.of(agentId));
    final var agent =
      agentDescriptions.get(agentId);

    /*
     * If the specific agent does not exist, this is a hard error. There's
     * no way the plan can be made to succeed if a required agent has been
     * deleted.
     */

    if (agent == null) {
      throw this.errorSpecificAgentNonexistent(agentId);
    }

    final var task =
      specific.task();
    final var workItem =
      this.createWorkItemForAgent(task, agent);

    if (this.agents.sendWorkItem(agentId, workItem)) {
      this.logInfo(
        "Agent %s received work item %s.",
        agentId,
        workItem.identifier().planElementName()
      );
      this.planUpdates.add(new AgentAcceptedTask(task.name(), agentId));
    } else {
      LOG.debug("Agent {} did not receive work item.", agentId);
    }
  }

  private void onPlanEventTaskRequiresMatchingAgent(
    final NPPlanTaskType task)
    throws NPDatabaseException, NPServerException
  {
    /*
     * Find all the agents that match the requirements of the task.
     */

    final var suitableAgents =
      this.agents.findSuitableAgentsFor(
        task.agentRequireWithLabel(),
        task.agentPreferWithLabel()
      );

    final var preferredAgents =
      suitableAgents.preferred();
    final var availableAgents =
      suitableAgents.available();

    final var targetAgents =
      preferredAgents.isEmpty() ? availableAgents : preferredAgents;

    if (targetAgents.isEmpty()) {
      return;
    }

    /*
     * Generate a work item for each agent, and offer the item to each
     * agent.
     */

    final var workItems =
      this.createWorkItemsFor(targetAgents, task);
    final var workItemsAccepted =
      new HashMap<NPAgentID, NPAgentWorkItem>();

    for (final var entry : workItems.entrySet()) {
      final var agentId =
        entry.getKey();
      final var workItem =
        entry.getValue();

      if (this.agents.offerWorkItem(agentId, workItem)) {
        LOG.debug("Agent {} accepted work item offer.", agentId);
        workItemsAccepted.put(agentId, workItem);
      } else {
        LOG.debug("Agent {} did not accept work item offer.", agentId);
      }
    }

    /*
     * Of the subset of agents that claimed to be able to accept the work,
     * try sending the work item to each agent in turn, stopping at the
     * first agent that accepts the work.
     */

    for (final var entry : workItemsAccepted.entrySet()) {
      final var agentId =
        entry.getKey();
      final var workItem =
        entry.getValue();

      if (this.agents.sendWorkItem(agentId, workItem)) {
        this.logInfo(
          "Agent %s received work item %s.",
          agentId,
          workItem.identifier().planElementName()
        );
        this.planUpdates.add(new AgentAcceptedTask(task.name(), agentId));
        return;
      } else {
        LOG.debug("Agent {} did not receive work item.", agentId);
      }
    }

    LOG.debug("No agents accepted a work item.");
  }

  private Map<NPAgentID, NPAgentDescription> findAgents(
    final Set<NPAgentID> agentIds)
    throws NPDatabaseException
  {
    final var results =
      new HashMap<NPAgentID, NPAgentDescription>();

    try (var connection = this.database.openConnection(NORTHPIKE_READ_ONLY);
         var transaction = connection.openTransaction()) {

      final var agentGet = transaction.queries(AgentGetType.class);
      for (final var agentId : agentIds) {
        final var agentOpt =
          agentGet.execute(new Parameters(agentId, false));
        if (agentOpt.isEmpty()) {
          continue;
        }

        final var agent = agentOpt.get();
        results.put(agentId, agent);
      }

      return Map.copyOf(results);
    }
  }

  private Map<NPAgentID, NPAgentWorkItem> createWorkItemsFor(
    final Set<NPAgentID> agentIds,
    final NPPlanTaskType task)
    throws NPDatabaseException, NPServerException
  {
    final var results =
      new HashMap<NPAgentID, NPAgentWorkItem>();

    final var agentDescriptions = this.findAgents(agentIds);
    for (final var agent : agentDescriptions.values()) {
      results.put(agent.id(), this.createWorkItemForAgent(task, agent));
    }

    return Map.copyOf(results);
  }

  private NPAgentWorkItem createWorkItemForAgent(
    final NPPlanTaskType task,
    final NPAgentDescription agent)
    throws NPServerException
  {
    final NPTEvaluationResult evaluated =
      this.planPreparation.toolExecutions()
        .get(task.name());

    final var toolExecution =
      task.toolExecution();
    final var toolReference =
      task.toolByReferenceName(toolExecution.name())
        .orElseThrow(() -> {
          return this.errorToolReferenceNonexistent(toolExecution.name());
        });

    final var toolsRequired = new HashSet<NPToolReference>();
    for (final var required : toolExecution.toolRequirements()) {
      toolsRequired.add(
        task.toolByReferenceName(required)
          .orElseThrow(() -> {
            return this.errorToolReferenceNonexistent(required);
          })
      );
    }

    final var metadata =
      this.createWorkItemMetadata(task);

    final var itemIdentifier =
      new NPWorkItemIdentifier(
        this.executionId,
        task.name().name()
      );

    return new NPAgentWorkItem(
      itemIdentifier,
      metadata,
      toolsRequired,
      new NPToolExecutionEvaluated(
        toolReference,
        evaluated.evaluateEnvironment(agent.environmentVariables()),
        evaluated.arguments()
      ),
      this.archiveLinks,
      task.lockAgentResources(),
      task.failurePolicy(),
      task.cleanPolicy()
    );
  }

  private Map<String, String> createWorkItemMetadata(
    final NPPlanTaskType task)
  {
    final var identifier = this.plan.identifier();
    return Map.ofEntries(
      Map.entry(
        this.strings.format(PLAN),
        identifier.name().toString()
      ),
      Map.entry(
        this.strings.format(PLAN_VERSION),
        Long.toUnsignedString(identifier.version())
      ),
      Map.entry(
        this.strings.format(TASK),
        task.name().toString()
      )
    );
  }

  private NPServerException errorToolReferenceNonexistent(
    final NPToolReferenceName ref)
  {
    return new NPServerException(
      this.strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(TOOL_REFERENCE),
          ref.toString()
        )
      ),
      Optional.empty()
    );
  }

  private void assignmentSucceeded()
  {
    LOG.debug("Assignment succeeded.");

    this.logAttributes.clear();
    this.logInfo("Assignment completed successfully.");

    this.setAssignmentExecutionState(
      new NPAssignmentExecutionStateSucceeded(
        this.timeCalculateCreated(),
        this.assignmentExecution,
        this.timeCalculateStarted(),
        this.timeCalculateEnded()
      ));
  }

  private OffsetDateTime timeCalculateCreated()
  {
    final var t = this.timeCreated;
    if (t == null) {
      this.timeCreated = this.clock.nowPrecise();
    }
    return this.timeCreated;
  }


  private OffsetDateTime timeCalculateStarted()
  {
    final var t = this.timeStarted;
    if (t == null) {
      this.timeStarted = this.clock.nowPrecise();
    }
    return this.timeStarted;
  }

  private OffsetDateTime timeCalculateEnded()
  {
    final var t = this.timeEnded;
    if (t == null) {
      this.timeEnded = this.clock.nowPrecise();
    }
    return this.timeEnded;
  }

  private void assignmentStart()
  {
    LOG.debug("Assignment started.");

    this.setAssignmentExecutionState(
      new NPAssignmentExecutionStateRunning(
        this.timeCalculateCreated(),
        this.assignmentExecution,
        this.timeCalculateStarted()
      ));
  }

  private void assignmentFailed()
  {
    LOG.debug("Assignment failed.");

    this.logAttributes.clear();
    this.logError("Assignment failed.");

    switch (this.executionState) {
      case final NPAssignmentExecutionStateCreatedType ignored -> {
        this.setAssignmentExecutionState(
          new NPAssignmentExecutionStateFailed(
            this.timeCalculateCreated(),
            this.assignmentExecution,
            this.timeCalculateStarted(),
            this.timeCalculateEnded()
          ));
      }
      default -> {
        this.setAssignmentExecutionState(
          new NPAssignmentExecutionStateCreationFailed(
            this.executionId,
            this.assignmentRequest,
            this.timeCalculateCreated()
          ));
      }
    }
  }

  private void assignmentCreateInitialState()
    throws NPException
  {
    /*
     * Setting up the initial assignment state might fail if the assignment
     * does not actually exist.
     */

    try {
      try (var connection = this.database.openConnection(NORTHPIKE);
           var transaction = connection.openTransaction()) {
        this.setAssignmentExecutionState(transaction, this.executionState);
        transaction.commit();
        this.assignment = this.findAssignment(transaction);
      }
    } catch (final NPException e) {
      this.setAssignmentExecutionState(
        new NPAssignmentExecutionStateCreationFailed(
          this.executionId,
          this.assignmentRequest,
          this.timeCalculateCreated()
        )
      );
      throw e;
    }
  }

  private void assignmentCreateExecution()
    throws NPException, InterruptedException
  {
    try {
      this.commit =
        this.repositories.commitGet(
          new NPCommitID(
            this.assignment.repositoryId(),
            this.assignmentRequest.commit()
          )
        );
      this.assignmentExecution =
        new NPAssignmentExecution(
          this.executionId,
          this.assignment,
          this.commit.id().commitId()
        );
    } catch (final NPException e) {
      this.setAssignmentExecutionState(
        new NPAssignmentExecutionStateCreationFailed(
          this.executionId,
          this.assignmentRequest,
          this.timeCalculateCreated()
        )
      );
      throw e;
    }
  }

  private NPAssignment findAssignment(
    final NPDatabaseTransactionType transaction)
    throws NPDatabaseException, NPServerException
  {
    return transaction.queries(AssignmentGetType.class)
      .execute(this.assignmentRequest.assignment())
      .orElseThrow(this::errorNonexistentAssignment);
  }

  private NPServerException errorNonexistentAssignment()
  {
    return new NPServerException(
      this.strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(ASSIGNMENT),
          this.assignmentRequest.assignment().value().value()
        ),
        Map.entry(
          this.strings.format(COMMIT),
          this.assignmentRequest.commit().value()
        )
      ),
      Optional.empty()
    );
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public void close()
  {
    this.closed.set(true);
  }

  @Override
  public void onSubscribe(
    final Subscription subscription)
  {
    subscription.request(Long.MAX_VALUE);
  }

  @Override
  public void onNext(
    final NPEventType item)
  {
    if (item instanceof final NPAgentWorkItemEventType agentEvent) {
      this.onAgentWorkItemEvent(agentEvent);
      return;
    }
  }

  private void onAgentWorkItemEvent(
    final NPAgentWorkItemEventType agentEvent)
  {
    if (!this.agentEventMatchesThisExecution(agentEvent)) {
      return;
    }

    switch (agentEvent) {
      case final NPAgentWorkItemAccepted accepted -> {
        this.onAgentEventWorkItemAccepted(accepted);
        return;
      }
      case final NPAgentWorkItemStatusChanged status -> {
        this.onAgentEventWorkItemStatusChanged(status);
        return;
      }
    }
  }

  private boolean agentEventMatchesThisExecution(
    final NPAgentWorkItemEventType event)
  {
    return Objects.equals(
      this.executionId,
      event.identifier().assignmentExecutionId()
    );
  }

  private void onAgentEventWorkItemStatusChanged(
    final NPAgentWorkItemStatusChanged event)
  {
    this.logAttributes.clear();
    this.logAttributes.putAll(event.asAttributes());

    switch (event.status()) {
      case WORK_ITEM_ACCEPTED -> {
        this.logInfo(
          "Agent %s accepted work item %s.",
          event.agentID(),
          event.identifier().planElementName()
        );
      }

      case WORK_ITEM_CREATED -> {
        this.logInfo(
          "Work item %s was created.",
          event.identifier().planElementName()
        );
      }

      case WORK_ITEM_RUNNING -> {

      }

      case WORK_ITEM_SUCCEEDED -> {
        this.logInfo(
          "Agent %s completed work item %s successfully.",
          event.agentID(),
          event.identifier().planElementName()
        );

        this.planUpdates.add(
          new AgentReportedTaskSuccess(
            new NPPlanElementName(event.identifier().planElementName()),
            event.agentID()
          )
        );
      }

      case WORK_ITEM_FAILED -> {
        this.logError(
          "Agent %s failed to complete work item %s.",
          event.agentID(),
          event.identifier().planElementName()
        );

        this.planUpdates.add(
          new AgentReportedTaskFailure(
            new NPPlanElementName(event.identifier().planElementName()),
            event.agentID()
          )
        );
      }
    }
  }

  private void onAgentEventWorkItemAccepted(
    final NPAgentWorkItemAccepted event)
  {
    this.planUpdates.add(
      new AgentAcceptedTask(
        new NPPlanElementName(event.identifier().planElementName()),
        event.agentID()
      )
    );
  }

  @Override
  public void onError(
    final Throwable throwable)
  {
    LOG.debug("Event handling failure: ", throwable);
  }

  @Override
  public void onComplete()
  {

  }

  /**
   * @return The execution identifier
   */

  public NPAssignmentExecutionID executionId()
  {
    return this.executionId;
  }

  private void setAssignmentExecutionState(
    final NPAssignmentExecutionStateType newState)
  {
    try (var connection = this.database.openConnection(NORTHPIKE);
         var transaction = connection.openTransaction()) {
      this.setAssignmentExecutionState(transaction, newState);
      transaction.commit();
    } catch (final NPDatabaseException e) {
      recordSpanException(e);
    }
  }

  /**
   * Set the assignment execution state.
   *
   * @param transaction The current transaction
   * @param newState    The new assignment execution state
   */

  private void setAssignmentExecutionState(
    final NPDatabaseTransactionType transaction,
    final NPAssignmentExecutionStateType newState)
  {
    if (LOG.isDebugEnabled()) {
      LOG.debug(
        "State {} -> {}",
        this.executionState.getClass().getSimpleName(),
        newState.getClass().getSimpleName()
      );
    }

    this.executionState = newState;
    this.events.emit(
      new NPAssignmentExecutionStatusChanged(this.executionState)
    );

    try {
      transaction.queries(AssignmentExecutionPutType.class)
        .execute(this.executionState);
    } catch (final NPDatabaseException e) {
      recordSpanException(e);
    }
  }
}
