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

package com.io7m.northpike.assignments;

import com.io7m.jaffirm.core.Preconditions;
import com.io7m.northpike.model.NPCommitID;

import java.util.Objects;
import java.util.UUID;

/**
 * An execution of an assignment.
 *
 * @param id         The execution ID
 * @param assignment The assignment
 * @param commit     The specific commit
 */

public record NPAssignmentExecution(
  UUID id,
  NPAssignment assignment,
  NPCommitID commit)
{
  /**
   * An execution of an assignment.
   *
   * @param id         The execution ID
   * @param assignment The assignment
   * @param commit     The specific commit
   */

  public NPAssignmentExecution
  {
    Objects.requireNonNull(id, "executionId");
    Objects.requireNonNull(assignment, "assignment");
    Objects.requireNonNull(commit, "commit");

    Preconditions.checkPreconditionV(
      Objects.equals(commit.repository(), assignment.repositoryId()),
      "Commit repository %s must match assignment repository %s",
      commit.repository(),
      assignment.repositoryId()
    );
  }
}
