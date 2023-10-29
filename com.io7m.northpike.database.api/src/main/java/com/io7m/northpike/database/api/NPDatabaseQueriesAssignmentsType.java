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

package com.io7m.northpike.database.api;


import com.io7m.northpike.model.NPPageSizes;
import com.io7m.northpike.model.NPSearchParametersType;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.NPTimeRange;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.NPWorkItemLogRecord;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionSearchParameters;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentSearchParameters;

import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The database queries involving assignments.
 */

public sealed interface NPDatabaseQueriesAssignmentsType
  extends NPDatabaseQueriesType
{
  /**
   * Update the given assignments.
   */

  non-sealed interface PutType
    extends NPDatabaseQueryType<NPAssignment, NPDatabaseUnit>,
    NPDatabaseQueriesAssignmentsType
  {

  }

  /**
   * Retrieve an assignment.
   */

  non-sealed interface GetType
    extends NPDatabaseQueryType<NPAssignmentName, Optional<NPAssignment>>,
    NPDatabaseQueriesAssignmentsType
  {

  }

  /**
   * Search assignments.
   */

  non-sealed interface SearchType
    extends NPDatabaseQueryType<NPAssignmentSearchParameters, NPAssignmentsPagedType>,
    NPDatabaseQueriesAssignmentsType
  {

  }

  /**
   * Search assignments.
   */

  non-sealed interface CommitsNotExecutedType
    extends NPDatabaseQueryType<CommitsNotExecutedType.Parameters, NPCommitSummaryPagedType>,
    NPDatabaseQueriesAssignmentsType
  {
    /**
     * The search parameters.
     *
     * @param assignment The assignment name
     * @param timeRange  Only return commits created within this time range
     * @param pageSize   The page size
     */

    record Parameters(
      NPAssignmentName assignment,
      NPTimeRange timeRange,
      long pageSize)
    {
      /**
       * The search parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(assignment, "assignment");
        Objects.requireNonNull(timeRange, "timeRange");
        pageSize = NPPageSizes.clampPageSize(pageSize);
      }
    }
  }

  /**
   * Update the given assignment execution.
   */

  non-sealed interface ExecutionPutType
    extends NPDatabaseQueryType<NPAssignmentExecutionStateType, NPDatabaseUnit>,
    NPDatabaseQueriesAssignmentsType
  {

  }

  /**
   * Retrieve an assignment execution.
   */

  non-sealed interface ExecutionGetType
    extends NPDatabaseQueryType<NPAssignmentExecutionID, Optional<NPAssignmentExecutionStateType>>,
    NPDatabaseQueriesAssignmentsType
  {

  }

  /**
   * Delete the given assignment execution.
   */

  non-sealed interface ExecutionDeleteType
    extends NPDatabaseQueryType<ExecutionDeleteType.Parameters, NPDatabaseUnit>,
    NPDatabaseQueriesAssignmentsType
  {
    /**
     * The scope of deletion.
     */

    enum DeletionScope
    {

      /**
       * Delete the logs associated with the execution.
       */

      DELETE_LOGS,

      /**
       * Delete the execution and everything associated with it.
       */

      DELETE_EVERYTHING
    }

    /**
     * The deletion parameters.
     *
     * @param execution The assignment execution
     * @param scope     The deletion scope
     */

    record Parameters(
      NPAssignmentExecutionID execution,
      DeletionScope scope)
    {
      /**
       * The deletion parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(execution, "execution");
        Objects.requireNonNull(scope, "scope");
      }
    }
  }

  /**
   * Search assignment executions.
   */

  non-sealed interface ExecutionSearchType
    extends NPDatabaseQueryType<
    NPAssignmentExecutionSearchParameters, NPAssignmentExecutionsPagedType>,
    NPDatabaseQueriesAssignmentsType
  {

  }

  /**
   * Add a log message to the assignment execution.
   */

  non-sealed interface ExecutionLogAddType
    extends NPDatabaseQueryType<ExecutionLogAddType.Parameters, NPDatabaseUnit>,
    NPDatabaseQueriesAssignmentsType
  {
    /**
     * The log parameters.
     *
     * @param execution  The assignment execution
     * @param type       The message type (such as "EXCEPTION")
     * @param message    The message
     * @param attributes The message attributes
     * @param exception  The associated exception, if any
     */

    record Parameters(
      NPAssignmentExecutionID execution,
      String type,
      String message,
      Map<String, String> attributes,
      Optional<NPStoredException> exception)
    {
      /**
       * The log parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(execution, "execution");
        Objects.requireNonNull(type, "type");
        Objects.requireNonNull(message, "line");
        Objects.requireNonNull(attributes, "attributes");
        Objects.requireNonNull(exception, "exception");
      }
    }
  }

  /**
   * Search execution logs.
   */

  non-sealed interface ExecutionLogListType
    extends NPDatabaseQueryType<ExecutionLogListType.Parameters, NPAssignmentExecutionLogPagedType>,
    NPDatabaseQueriesAssignmentsType
  {
    /**
     * The log parameters.
     *
     * @param execution     The assignment execution
     * @param timeAscending {@code true} if lines should be in time-ascending order
     * @param pageSize      The page size
     */

    record Parameters(
      NPAssignmentExecutionID execution,
      boolean timeAscending,
      long pageSize)
      implements NPSearchParametersType
    {
      /**
       * The log parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(execution, "execution");
        pageSize = NPPageSizes.clampPageSize(pageSize);
      }
    }
  }

  /**
   * Mark all non-completed executions as being cancelled.
   */

  non-sealed interface ExecutionsCancelAllType
    extends NPDatabaseQueryType<NPDatabaseUnit, Long>,
    NPDatabaseQueriesAssignmentsType
  {

  }

  /**
   * Obtain the work items in the given execution.
   */

  non-sealed interface ExecutionWorkItemsType
    extends NPDatabaseQueryType<NPAssignmentExecutionID, Set<NPWorkItem>>,
    NPDatabaseQueriesAssignmentsType
  {

  }

  /**
   * Update the given work item.
   */

  non-sealed interface WorkItemPutType
    extends NPDatabaseQueryType<NPWorkItem, NPDatabaseUnit>,
    NPDatabaseQueriesAssignmentsType
  {

  }

  /**
   * Retrieve a work item.
   */

  non-sealed interface WorkItemGetType
    extends NPDatabaseQueryType<NPWorkItemIdentifier, Optional<NPWorkItem>>,
    NPDatabaseQueriesAssignmentsType
  {

  }

  /**
   * Add a line of output to the given work item.
   */

  non-sealed interface WorkItemLogAddType
    extends NPDatabaseQueryType<NPWorkItemLogRecord, NPDatabaseUnit>,
    NPDatabaseQueriesAssignmentsType
  {

  }
}
