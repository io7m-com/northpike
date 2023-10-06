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


package com.io7m.northpike.server.internal.agents;

import com.io7m.jaffirm.core.Preconditions;
import com.io7m.jmulticlose.core.CloseableType;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentLabelName;
import com.io7m.northpike.model.NPAgentWorkItem;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.repetoir.core.RPServiceType;

import java.util.Objects;
import java.util.Set;
import java.util.concurrent.CompletableFuture;

/**
 * The service to which agents connect.
 */

public interface NPAgentServiceType
  extends CloseableType, RPServiceType
{
  /**
   * Start the service running.
   *
   * @return A future representing the service startup
   */

  CompletableFuture<Void> start();

  /**
   * Find the connected agents that match the given expressions.
   *
   * @param require Agents must match this label expression
   * @param prefer  Agents comparisons this label expression will be preferred
   *
   * @return The agents
   */

  NPSuitableAgents findSuitableAgentsFor(
    NPComparisonSetType<NPAgentLabelName> require,
    NPComparisonSetType<NPAgentLabelName> prefer);

  /**
   * Offer the given work item to the given agent.
   *
   * @param agent    The agent
   * @param workItem The work item
   *
   * @return {@code true} if the given agent can accept the work
   */

  boolean offerWorkItem(
    NPAgentID agent,
    NPAgentWorkItem workItem
  );

  /**
   * Send the given work item to the given agent. The agent is assumed to
   * have previously accepted an offer of the work.
   *
   * @param agent    The agent
   * @param workItem The work item
   *
   * @return {@code true} if the given agent accepts the work
   *
   * @see #offerWorkItem(NPAgentID, NPAgentWorkItem)
   */

  boolean sendWorkItem(
    NPAgentID agent,
    NPAgentWorkItem workItem);

  /**
   * @return The set of connected agents
   */

  Set<NPAgentID> findAgentsConnected();

  /**
   * @return The set of currently executing work items
   */

  Set<NPWorkItem> findAgentWorkItemsExecuting();

  /**
   * The suitable agents.
   *
   * @param available The available agents
   * @param preferred The preferred agents
   */

  record NPSuitableAgents(
    Set<NPAgentID> available,
    Set<NPAgentID> preferred)
  {
    /**
     * The suitable agents.
     */

    public NPSuitableAgents
    {
      Objects.requireNonNull(available, "available");
      Objects.requireNonNull(preferred, "preferred");

      Preconditions.checkPreconditionV(
        available.containsAll(preferred),
        "Preferred set must be a subset of the available set."
      );

      available = Set.copyOf(available);
      preferred = Set.copyOf(preferred);
    }
  }
}
