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


package com.io7m.northpike.plans;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPAgentLabelMatchType;

import java.util.Set;

/**
 * A task within a plan.
 */

public non-sealed interface NPPlanTaskType
  extends NPPlanElementType
{
  /**
   * In order for a task to be executed by an agent, the agent must match
   * this expression.
   *
   * @return The expression against which to match agents
   */

  NPAgentLabelMatchType agentRequireWithLabel();

  /**
   * When multiple agents match against the {@link #agentRequireWithLabel()}
   * expression, agents matching this expression will be preferred over others.
   *
   * @return The expression against which to match agents
   */

  NPAgentLabelMatchType agentPreferWithLabel();

  /**
   * @return The set of resources that will be locked on the agent during
   * task execution
   */

  Set<RDottedName> lockAgentResources();

  /**
   * @return The tool execution for this task
   */

  NPPlanToolExecution toolExecution();
}
