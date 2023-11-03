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


package com.io7m.northpike.agent.internal.worker;

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.internal.NPAgentResources;
import com.io7m.northpike.agent.internal.NPAgentTaskType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorType;
import com.io7m.northpike.strings.NPStrings;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The task that handles work for the agent.
 */

public final class NPAgentWorkerTaskExecutor implements NPAgentTaskType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentWorkerTaskExecutor.class);

  private final AtomicBoolean closed;
  private final NPStrings strings;
  private final NPAWorkExecutorType workExec;
  private final CloseableCollectionType<NPAgentException> resources;

  private NPAgentWorkerTaskExecutor(
    final NPStrings inStrings,
    final NPAWorkExecutorType inWorkExec,
    final CloseableCollectionType<NPAgentException> inResources)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.workExec =
      Objects.requireNonNull(inWorkExec, "workExec");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.closed =
      new AtomicBoolean(false);
  }

  /**
   * The task that handles work for the agent.
   *
   * @param strings  The strings
   * @param workExec The work executor
   *
   * @return An agent
   *
   * @throws InterruptedException On interruption
   */

  public static NPAgentWorkerTaskExecutor open(
    final NPStrings strings,
    final NPAWorkExecutorType workExec)
    throws InterruptedException
  {
    Objects.requireNonNull(strings, "strings");
    Objects.requireNonNull(workExec, "workExec");

    final var resources =
      NPAgentResources.createResources();

    return new NPAgentWorkerTaskExecutor(
      strings,
      workExec,
      resources
    );
  }

  @Override
  public void run()
  {
    LOG.debug("Start");

    while (!this.isClosed()) {
      try {
        Thread.sleep(1_000L);
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
      }
    }
  }

  @Override
  public void close()
    throws NPAgentException
  {
    if (this.closed.compareAndSet(false, true)) {
      LOG.debug("Close");
      this.resources.close();
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public String name()
  {
    return "com.io7m.northpike.agent.work_controller";
  }
}
