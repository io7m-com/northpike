/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.agent.locks;

import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentResourceName;
import com.io7m.repetoir.core.RPServiceType;

import java.time.Duration;
import java.util.Set;
import java.util.concurrent.TimeoutException;

/**
 * The agent resource lock service.
 */

public interface NPAgentResourceLockServiceType
  extends RPServiceType
{
  /**
   * @return The default duration to wait for locks before timing out
   */

  Duration lockTimeoutDefault();

  /**
   * Obtain a lock on all the resources for agent {@code agent}. If no
   * lock can be obtained on all resources before the given timeout elapses,
   * {@code TimeoutException} is raised without affecting any resources.
   *
   * @param agent     The agent
   * @param resources The resources
   * @param timeout   The timeout
   *
   * @return The locked resources
   *
   * @throws TimeoutException     If no lock can be obtained
   * @throws InterruptedException On interruption
   */

  NPAgentResourceLockSetType lock(
    NPAgentLocalName agent,
    Set<NPAgentResourceName> resources,
    Duration timeout)
    throws TimeoutException, InterruptedException;

  /**
   * Obtain a lock on all the resources for agent {@code agent}. If no
   * lock can be obtained on all resources before the timeout elapses,
   * {@code TimeoutException} is raised without affecting any resources.
   *
   * @param agent     The agent
   * @param resources The resources
   *
   * @return The locked resources
   *
   * @throws TimeoutException     If no lock can be obtained
   * @throws InterruptedException On interruption
   */

  default NPAgentResourceLockSetType lockWithDefaultTimeout(
    final NPAgentLocalName agent,
    final Set<NPAgentResourceName> resources)
    throws TimeoutException, InterruptedException
  {
    return this.lock(agent, resources, this.lockTimeoutDefault());
  }

  /**
   * @param agent    The agent
   * @param resource The resource
   *
   * @return {@code true} if the given agent holds the given resource
   */

  boolean isLockedBy(
    NPAgentLocalName agent,
    NPAgentResourceName resource);
}
