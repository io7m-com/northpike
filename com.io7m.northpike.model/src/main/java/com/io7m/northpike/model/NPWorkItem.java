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


package com.io7m.northpike.model;

import com.io7m.northpike.model.agents.NPAgentID;

import java.util.Objects;
import java.util.Optional;

/**
 * A work item within an assignment.
 *
 * @param identifier    The identifier
 * @param selectedAgent The assigned agent
 * @param status        The status
 */

public record NPWorkItem(
  NPWorkItemIdentifier identifier,
  Optional<NPAgentID> selectedAgent,
  NPWorkItemStatus status)
{
  /**
   * A work item within an assignment.
   *
   * @param identifier    The identifier
   * @param selectedAgent The assigned agent
   * @param status        The status
   */

  public NPWorkItem
  {
    Objects.requireNonNull(identifier, "identifier");
    Objects.requireNonNull(selectedAgent, "assignedAgent");
    Objects.requireNonNull(status, "status");
  }

  /**
   * @param id The agent ID
   *
   * @return {@code true} if this work item has the given agent
   */

  public boolean hasAgent(
    final NPAgentID id)
  {
    return this.selectedAgent.equals(Optional.of(id));
  }
}
