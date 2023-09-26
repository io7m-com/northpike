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
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.repetoir.core.RPServiceType;

import java.util.List;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;

/**
 * The assignment service.
 */

public interface NPAssignmentServiceType
  extends CloseableType, RPServiceType
{
  /**
   * An execution in progress.
   *
   * @param request     The request
   * @param executionId The execution ID
   * @param future      The future representing the operation
   */

  record NPExecutionInProgress(
    NPAssignmentExecutionRequest request,
    NPAssignmentExecutionID executionId,
    CompletableFuture<NPAssignmentExecutionStateType> future)
  {
    /**
     * An execution in progress.
     */

    public NPExecutionInProgress
    {
      Objects.requireNonNull(request, "request");
      Objects.requireNonNull(executionId, "executionId");
      Objects.requireNonNull(future, "future");
    }
  }

  /**
   * Request that an assignment begin executing.
   *
   * @param request The request
   *
   * @return The operation in progress
   */

  NPExecutionInProgress requestExecution(
    NPAssignmentExecutionRequest request);

  /**
   * @return A read-only snapshot of the currently enqueued requests
   */

  List<NPAssignmentExecutionRequest> requestsEnqueued();

  @Override
  void close()
    throws NPException;
}
