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
import com.io7m.northpike.assignments.NPAssignment;
import com.io7m.northpike.assignments.NPAssignmentExecution;
import com.io7m.northpike.assignments.NPAssignmentExecutionCreated;
import com.io7m.northpike.assignments.NPAssignmentExecutionRunning;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentWorkItem;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPArchiveWithLinks;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPToolExecutionEvaluated;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.plans.NPPlanElementName;
import com.io7m.northpike.plans.NPPlanIdentifier;
import com.io7m.northpike.plans.NPPlanTaskType;
import com.io7m.northpike.plans.NPPlanType;
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
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusSucceeded;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentAcceptedTask;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.preparation.NPPlanPreparation;
import com.io7m.northpike.plans.preparation.NPPlanPreparationType;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemAccepted;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemEventType;
import com.io7m.northpike.server.internal.agents.NPAgentWorkItemStatusChanged;
import com.io7m.northpike.server.internal.archives.NPArchiveServiceType;
import com.io7m.northpike.server.internal.clock.NPClockServiceType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPEventType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.toolexec.NPTXParserFactoryType;
import com.io7m.northpike.toolexec.evaluator.NPTXEvaluator;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Flow;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_ID;
import static com.io7m.northpike.strings.NPStringConstants.COMMIT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;
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
  implements Runnable, CloseableType, Flow.Subscriber<NPEventType>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAssignmentTask.class);

  private final NPAgentServiceType agents;
  private final NPArchiveServiceType archives;
  private final Set<NPPlanParserFactoryType> planParsers;
  private final Set<NPTXParserFactoryType> toolExecParsers;
  private final NPStrings strings;
  private final NPAssignment assignment;
  private final NPClockServiceType clock;
  private final NPCommitID commitId;
  private final NPDatabaseType database;
  private final NPRepositoryServiceType repositories;
  private final NPEventServiceType events;
  private final NPTelemetryServiceType telemetry;
  private final AtomicBoolean closed;
  private final ConcurrentLinkedQueue<NPPlanEvaluationUpdateType> planUpdates;
  private NPAssignmentExecution execution;
  private NPPlanType plan;
  private NPPlanEvaluationType planEvaluator;
  private NPPlanPreparationType planPreparation;
  private NPArchive archive;
  private NPCommit commit;

  private NPAssignmentTask(
    final NPDatabaseType inDatabase,
    final NPClockServiceType inClock,
    final NPEventServiceType inEvents,
    final NPTelemetryServiceType inTelemetry,
    final NPAgentServiceType inAgents,
    final NPRepositoryServiceType inRepositories,
    final NPArchiveServiceType inArchives,
    final Set<NPPlanParserFactoryType> inParserFactories,
    final Set<NPTXParserFactoryType> inToolExecParsers,
    final NPStrings inStrings,
    final NPAssignment inAssignment,
    final NPCommitID inCommit)
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
    this.toolExecParsers =
      Objects.requireNonNull(inToolExecParsers, "toolExecParsers");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.assignment =
      Objects.requireNonNull(inAssignment, "assignment");
    this.commitId =
      Objects.requireNonNull(inCommit, "commit");

    this.closed =
      new AtomicBoolean(false);

    this.planUpdates =
      new ConcurrentLinkedQueue<>();
    this.execution =
      new NPAssignmentExecution(
        UUID.randomUUID(),
        this.assignment,
        this.commitId,
        new NPAssignmentExecutionCreated(this.clock.now())
      );

    this.events.events()
      .subscribe(this);
  }

  /**
   * Create a new assignment task.
   *
   * @param services   The service directory
   * @param assignment The assignment
   * @param commit     The commit to build
   *
   * @return A new assignment task
   */

  public static NPAssignmentTask create(
    final RPServiceDirectoryType services,
    final NPAssignment assignment,
    final NPCommitID commit)
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
      Set.copyOf(services.optionalServices(NPTXParserFactoryType.class)),
      services.requireService(NPStrings.class),
      assignment,
      commit
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
        .spanBuilder("AssignmentExecution")
        .setAttribute("ExecutionID", this.execution.executionId().toString())
        .setAttribute("Assignment", this.assignment.name().toString())
        .setAttribute("PlanName", this.assignment.plan().name().toString())
        .setAttribute("PlanVersion", this.assignment.plan().version())
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      try {
        this.assignmentInitialize();
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
    } finally {
      span.end();
    }
  }

  private void assignmentCompilePlan()
    throws NPException
  {
    try (var connection = this.database.openConnection(NORTHPIKE)) {
      try (var transaction = connection.openTransaction()) {
        final var planGet =
          transaction.queries(NPDatabaseQueriesPlansType.GetType.class);
        final var toolGet =
          transaction.queries(NPDatabaseQueriesToolsType.GetExecutionDescriptionType.class);
        final var commitGet =
          transaction.queries(NPDatabaseQueriesRepositoriesType.CommitGetType.class);

        this.commit =
          commitGet.execute(this.commitId)
            .orElseThrow(this::errorCommitNonexistent);

        final var planOpt =
          planGet.execute(new NPDatabaseQueriesPlansType.GetType.Parameters(
            this.assignment.plan(),
            this.planParsers
          ));

        if (planOpt.isEmpty()) {
          throw this.errorPlanNonexistent(this.assignment.plan());
        }

        this.plan =
          planOpt.get().toPlan(this.strings);

        this.planEvaluator =
          NPPlanEvaluation.create(
            this.clock.clock(),
            this.plan
          );

        final var compiler =
          new NPAssignmentToolExecutionCompiler(
            this.strings,
            this.toolExecParsers,
            toolGet
          );

        final var archiveLinks =
          this.archives.linksForArchive(this.archive);

        this.planPreparation =
          NPPlanPreparation.forCommit(
            compiler,
            this.commit,
            new NPArchiveWithLinks(this.archive, archiveLinks),
            this.plan
          );

        LOG.info("Compiled plan {}", this.plan);
      }
    }
  }

  private NPServerException errorCommitNonexistent()
  {
    return new NPServerException(
      this.strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(COMMIT),
          this.commitId.value()
        ),
        Map.entry(
          this.strings.format(REPOSITORY),
          this.commitId.repository().toString()
        )
      ),
      Optional.empty()
    );
  }

  private NPServerException errorPlanNonexistent(
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
      this.archive =
        this.repositories.createArchiveFor(this.commitId)
          .get(5L, TimeUnit.MINUTES);
    } catch (final ExecutionException e) {
      throw (Exception) e.getCause();
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

      if (planStatus instanceof StatusFailed) {
        this.assignmentFailed();
        return;
      }
      if (planStatus instanceof StatusSucceeded) {
        this.assignmentSucceeded();
        return;
      }
      pauseQuietly();
    }
  }

  private void onPlanEvent(
    final NPPlanEvaluationEventType event)
    throws NPException
  {
    LOG.debug("Plan event: {}", event);

    if (event instanceof ElementBecameReady) {
      return;
    }

    if (event instanceof ElementFailed) {
      return;
    }

    if (event instanceof ElementSucceeded) {
      return;
    }

    if (event instanceof final TaskRequiresSpecificAgent specific) {
      this.onPlanEventTaskRequiresSpecificAgent(specific);
      return;
    }

    if (event instanceof final TaskRequiresMatchingAgent matching) {
      this.onPlanEventTaskRequiresMatchingAgent(matching.task());
      return;
    }

    if (event instanceof TaskAgentSelectionTimedOut) {
      return;
    }

    if (event instanceof TaskExecutionTimedOut) {
      return;
    }

    throw new IllegalStateException(
      "Unrecognized plan event: %s".formatted(event)
    );
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
      LOG.debug("Agent {} received work item.", agentId);
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
        LOG.debug("Agent {} received work item.", agentId);
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

    try (var connection =
           this.database.openConnection(NORTHPIKE)) {
      try (var transaction =
             connection.openTransaction()) {
        final var agentGet =
          transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);

        for (final var agentId : agentIds) {
          final var agentOpt =
            agentGet.execute(agentId);
          if (agentOpt.isEmpty()) {
            continue;
          }

          final var agent = agentOpt.get();
          results.put(agentId, agent);
        }

        return Map.copyOf(results);
      }
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
    final var typeChecked =
      this.planPreparation.toolExecutions()
        .get(task.name());

    final var evaluated =
      new NPTXEvaluator(agent.environmentVariables(), typeChecked)
        .evaluate();

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
        this.execution.executionId(),
        task.name().name()
      );

    return new NPAgentWorkItem(
      itemIdentifier,
      metadata,
      toolsRequired,
      new NPToolExecutionEvaluated(
        toolReference,
        evaluated.environment(),
        evaluated.arguments()
      ),
      task.lockAgentResources(),
      task.failurePolicy()
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
    throws NPDatabaseException
  {
    LOG.debug("Assignment succeeded.");

    this.execution =
      this.execution.withStatus(
        this.execution.status().succeed(this.clock.now())
      );

    this.executionUpdateDatabase();
    this.emitStatusChangeEvent();
  }

  private void assignmentStart()
    throws NPDatabaseException
  {
    LOG.debug("Assignment started.");

    this.execution =
      this.execution.withStatus(
        new NPAssignmentExecutionRunning(
          this.execution.status().timeCreated(),
          this.clock.now()
        )
      );

    this.executionUpdateDatabase();
    this.emitStatusChangeEvent();
  }

  private void emitStatusChangeEvent()
  {
    this.events.emit(new NPAssignmentExecutionStatusChanged(this.execution));
  }

  private void assignmentFailed()
    throws NPDatabaseException
  {
    LOG.debug("Assignment failed.");

    this.execution =
      this.execution.withStatus(
        this.execution.status().fail(this.clock.now())
      );
    this.executionUpdateDatabase();
    this.emitStatusChangeEvent();
  }

  private void assignmentInitialize()
    throws NPDatabaseException
  {
    this.executionUpdateDatabase();
    this.emitStatusChangeEvent();
  }

  private void executionUpdateDatabase()
    throws NPDatabaseException
  {
    try (var connection = this.database.openConnection(NORTHPIKE)) {
      try (var transaction = connection.openTransaction()) {
        transaction.queries(NPDatabaseQueriesAssignmentsType.ExecutionPutType.class)
          .execute(this.execution);
        transaction.commit();
      }
    }
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
    final Flow.Subscription subscription)
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

    if (agentEvent instanceof final NPAgentWorkItemAccepted accepted) {
      this.onAgentEventWorkItemAccepted(accepted);
      return;
    }

    if (agentEvent instanceof final NPAgentWorkItemStatusChanged status) {
      this.onAgentEventWorkItemStatusChanged(status);
      return;
    }
  }

  private boolean agentEventMatchesThisExecution(
    final NPAgentWorkItemEventType event)
  {
    return Objects.equals(
      this.execution.executionId(),
      event.identifier().assignmentExecutionId()
    );
  }

  private void onAgentEventWorkItemStatusChanged(
    final NPAgentWorkItemStatusChanged event)
  {
    switch (event.status()) {
      case WORK_ITEM_CREATED, WORK_ITEM_ACCEPTED, WORK_ITEM_RUNNING -> {

      }

      case WORK_ITEM_SUCCEEDED -> {
        this.planUpdates.add(
          new NPPlanEvaluationUpdateType.AgentReportedTaskSuccess(
            new NPPlanElementName(event.identifier().planElementName()),
            event.agentID()
          )
        );
      }

      case WORK_ITEM_FAILED -> {
        this.planUpdates.add(
          new NPPlanEvaluationUpdateType.AgentReportedTaskFailure(
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
      new NPPlanEvaluationUpdateType.AgentAcceptedTask(
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
   * @return The assignment execution
   */

  public NPAssignmentExecution execution()
  {
    return this.execution;
  }
}
