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


package com.io7m.northpike.repository.jgit.internal;

import com.io7m.northpike.scm_repository.spi.NPSCMEventType;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryException;
import com.io7m.northpike.scm_repository.spi.NPSCMTaskCompletedFailure;
import com.io7m.northpike.scm_repository.spi.NPSCMTaskCompletedSuccessfully;
import com.io7m.northpike.scm_repository.spi.NPSCMTaskInProgress;
import com.io7m.northpike.scm_repository.spi.NPSCMTaskStarted;
import com.io7m.northpike.strings.NPStringConstantType;
import org.eclipse.jgit.lib.ProgressMonitor;

import java.util.Objects;
import java.util.UUID;
import java.util.concurrent.SubmissionPublisher;

final class NPSCMJTask implements ProgressMonitor
{
  private final UUID taskId;
  private final SubmissionPublisher<NPSCMEventType> events;
  private int workTotal;
  private int workNow;

  NPSCMJTask(
    final SubmissionPublisher<NPSCMEventType> inEvents,
    final NPStringConstantType inMessage)
  {
    this.events =
      Objects.requireNonNull(inEvents, "events");
    this.taskId =
      UUID.randomUUID();

    this.events.submit(new NPSCMTaskStarted(this.taskId, inMessage));
  }

  @Override
  public void start(
    final int totalTasks)
  {

  }

  @Override
  public void beginTask(
    final String title,
    final int totalWork)
  {
    this.workTotal = totalWork;
    this.workNow = 0;
  }

  @Override
  public void update(
    final int completed)
  {
    this.workNow += completed;

    if (this.workTotal != 0) {
      this.events.submit(
        new NPSCMTaskInProgress(
          this.taskId,
          (double) this.workNow / (double) this.workTotal
        )
      );
    } else {
      this.events.submit(
        new NPSCMTaskInProgress(this.taskId, 0.0)
      );
    }
  }

  @Override
  public void endTask()
  {

  }

  @Override
  public boolean isCancelled()
  {
    return false;
  }

  @Override
  public void showDuration(
    final boolean enabled)
  {

  }

  public void onFailed(
    final NPSCMRepositoryException ex)
  {
    this.events.submit(new NPSCMTaskCompletedFailure(this.taskId, ex));
  }

  public void onCompleted()
  {
    this.events.submit(new NPSCMTaskCompletedSuccessfully(this.taskId));
  }
}
