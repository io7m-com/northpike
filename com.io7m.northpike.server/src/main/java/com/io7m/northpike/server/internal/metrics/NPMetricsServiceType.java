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

package com.io7m.northpike.server.internal.metrics;

import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.repetoir.core.RPServiceType;

import java.time.Duration;

/**
 * The interface exposed by the metrics service.
 */

public interface NPMetricsServiceType extends AutoCloseable, RPServiceType
{
  /**
   * Set the number of connected agents.
   *
   * @param count The number of connected agents
   */

  void setAgentsConnected(int count);

  /**
   * Set the number of connected users.
   *
   * @param count The number of connected users
   */

  void setUsersConnected(int count);

  /**
   * Set the number of assignments currently executing.
   *
   * @param count The number of assignments executing
   */

  void setAssignmentsExecuting(int count);

  /**
   * Set the number of requests currently enqueued.
   *
   * @param count The number of assignments requests in the queue
   */

  void setAssignmentsQueueSize(int count);

  /**
   * Report that the given agent is connected with the given latency.
   *
   * @param agentId  The agent ID
   * @param duration The latency
   */

  void setAgentLatency(
    NPAgentID agentId,
    Duration duration);
}
