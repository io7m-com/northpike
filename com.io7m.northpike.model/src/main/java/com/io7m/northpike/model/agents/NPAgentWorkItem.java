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


package com.io7m.northpike.model.agents;

import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPCleanPolicyType;
import com.io7m.northpike.model.NPFailurePolicyType;
import com.io7m.northpike.model.NPToolExecutionEvaluated;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPWorkItemIdentifier;

import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * A single, complete item of work for an agent to execute.
 *
 * @param identifier    The work item identifier
 * @param metadata      The descriptive metadata
 * @param toolsRequired The required tools
 * @param toolExecution The tool execution
 * @param archiveLinks  The archive links
 * @param lockResources The resources on the agent that must be locked
 * @param failurePolicy The failure policy
 * @param cleanPolicy   The workspace cleanup policy
 */

public record NPAgentWorkItem(
  NPWorkItemIdentifier identifier,
  Map<String, String> metadata,
  Set<NPToolReference> toolsRequired,
  NPToolExecutionEvaluated toolExecution,
  NPArchiveLinks archiveLinks,
  Set<NPAgentResourceName> lockResources,
  NPFailurePolicyType failurePolicy,
  NPCleanPolicyType cleanPolicy)
{
  /**
   * A single, complete item of work for an agent to execute.
   *
   * @param identifier    The work item identifier
   * @param metadata      The descriptive metadata
   * @param toolsRequired The required tools
   * @param toolExecution The tool execution
   * @param archiveLinks  The archive links
   * @param lockResources The resources on the agent that must be locked
   * @param failurePolicy The failure policy
   * @param cleanPolicy   The workspace cleanup policy
   */

  public NPAgentWorkItem
  {
    Objects.requireNonNull(metadata, "metadata");
    Objects.requireNonNull(toolsRequired, "toolsRequired");
    Objects.requireNonNull(toolExecution, "toolExecution");
    Objects.requireNonNull(lockResources, "lockResources");
    Objects.requireNonNull(archiveLinks, "archiveLinks");
    Objects.requireNonNull(failurePolicy, "failurePolicy");
    Objects.requireNonNull(cleanPolicy, "cleanPolicy");

    metadata = Map.copyOf(metadata);
    toolsRequired = Set.copyOf(toolsRequired);
    lockResources = Set.copyOf(lockResources);
  }
}
