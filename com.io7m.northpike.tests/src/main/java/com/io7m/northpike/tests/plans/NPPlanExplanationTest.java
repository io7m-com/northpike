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


package com.io7m.northpike.tests.plans;

import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.plans.NPPlanToolExecution;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.analysis.NPPlanExplanation;
import com.io7m.northpike.plans.analysis.NPPlanExplanationType;
import com.io7m.northpike.strings.NPStringConstantApplied;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.verona.core.Version;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.Duration;
import java.util.List;
import java.util.Locale;
import java.util.Set;

import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_BARRIER_BECOMES_READY_EMPTY;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_DONE;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_EMPTY;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_AGENT_TIMEOUT;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_BECOMES_READY_DEPENDENCIES;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_BECOMES_READY_EMPTY;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_EXECUTION_TIMEOUT;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_REQUIRES_MATCHING_AGENT;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_REQUIRES_SPECIFIC_AGENT;
import static org.junit.jupiter.api.Assertions.assertEquals;

@Timeout(5L)
public final class NPPlanExplanationTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPPlanExplanationTest.class);

  private NPStrings strings;

  @BeforeEach
  public void setup()
  {
    this.strings = NPStrings.create(Locale.ROOT);
  }

  /**
   * Empty plans succeed immediately.
   *
   * @throws Exception On errors
   */

  @Test
  public void testEmptySucceedsImmediately()
    throws Exception
  {
    final var plan =
      NPPlans.builder(this.strings, "p", 1L)
        .build();

    final var explanation =
      NPPlanExplanation.explain(this.strings, plan);

    final var messages =
      this.dumpMessages(explanation);

    assertEquals(PLAN_EXPLAIN_EMPTY, messages.get(0));
    assertEquals(1, messages.size());
  }

  /**
   * A simple barrier example.
   *
   * @throws Exception On errors
   */

  @Test
  public void testBarriers0()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(this.strings, "p", 1L);

    final var b0 =
      planBuilder.addBarrier("b0");
    final var b1 =
      planBuilder.addBarrier("b1");
    final var b2 =
      planBuilder.addBarrier("b2");

    b2.addDependsOn(b1.name());
    b1.addDependsOn(b0.name());

    final var plan =
      planBuilder.build();

    final var explanation =
      NPPlanExplanation.explain(this.strings, plan);

    final var messages =
      this.dumpMessages(explanation);

    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_EMPTY,
      constantOf(messages, 0)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 1)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 2)
    );
    assertEquals(
      PLAN_EXPLAIN_DONE,
      messages.get(3)
    );
    assertEquals(4, messages.size());
  }

  private List<NPStringConstantType> dumpMessages(
    final NPPlanExplanationType explanation)
  {
    final var messages = explanation.messages();
    messages.forEach(msg -> LOG.debug(
      "message: {}",
      this.strings.format(msg).trim()));
    return messages;
  }

  /**
   * A simple parallel barrier example.
   *
   * @throws Exception On errors
   */

  @Test
  public void testBarriers1()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(this.strings, "p", 1L);

    final var b0_0 =
      planBuilder.addBarrier("b0_0");
    final var b0_1 =
      planBuilder.addBarrier("b0_1");
    final var b0_2 =
      planBuilder.addBarrier("b0_2");

    b0_2.addDependsOn(b0_1.name());
    b0_1.addDependsOn(b0_0.name());

    final var b1_0 =
      planBuilder.addBarrier("b1_0");
    final var b1_1 =
      planBuilder.addBarrier("b1_1");
    final var b1_2 =
      planBuilder.addBarrier("b1_2");

    b1_2.addDependsOn(b1_1.name());
    b1_1.addDependsOn(b1_0.name());

    final var b2_0 =
      planBuilder.addBarrier("b2_0");
    final var b2_1 =
      planBuilder.addBarrier("b2_1");
    final var b2_2 =
      planBuilder.addBarrier("b2_2");

    b2_2.addDependsOn(b2_1.name());
    b2_1.addDependsOn(b2_0.name());

    final var b_end =
      planBuilder.addBarrier("b_end");

    b_end.addDependsOn(b0_2.name());
    b_end.addDependsOn(b1_2.name());
    b_end.addDependsOn(b2_2.name());

    final var plan =
      planBuilder.build();

    final var explanation =
      NPPlanExplanation.explain(this.strings, plan);

    final var messages =
      this.dumpMessages(explanation);

    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_EMPTY,
      constantOf(messages, 0)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_EMPTY,
      constantOf(messages, 1)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_EMPTY,
      constantOf(messages, 2)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 3)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 4)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 5)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 6)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 7)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 8)
    );
    assertEquals(
      PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 9)
    );
    assertEquals(
      PLAN_EXPLAIN_DONE,
      messages.get(10)
    );
    assertEquals(11, messages.size());
  }

  private static NPStringConstantType constantOf(
    final List<NPStringConstantType> messages,
    final int index)
  {
    return ((NPStringConstantApplied) messages.get(index)).constant();
  }

  /**
   * A simple task example.
   *
   * @throws Exception On errors
   */

  @Test
  public void testTasks0()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(this.strings, "p", 1L);

    final var toolExec =
      new NPPlanToolExecution(
        NPToolReferenceName.of("texec"),
        NPToolExecutionIdentifier.of("te", 1L),
        Set.of()
      );

    planBuilder.addToolReference(new NPToolReference(
      NPToolReferenceName.of("texec"),
      NPToolName.of("arg"),
      Version.of(1, 0, 0)
    ));

    final var t0 =
      planBuilder.addTask("t0")
        .setToolExecution(toolExec);

    final var t1 =
      planBuilder.addTask("t1")
        .setToolExecution(toolExec);

    t1.addDependsOn(t0.name());

    final var agent0 =
      NPAgentID.of("c170409e-ccf1-4c2b-99c0-bf77fc213c7a");
    final var agent1 =
      NPAgentID.of("6e034f18-a4ee-4161-8ce3-d86986064c65");

    final var plan =
      planBuilder.build();

    final var explanation =
      NPPlanExplanation.explain(this.strings, plan);

    final var messages =
      this.dumpMessages(explanation);

    assertEquals(
      PLAN_EXPLAIN_TASK_BECOMES_READY_EMPTY,
      constantOf(messages, 0)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_REQUIRES_MATCHING_AGENT,
      constantOf(messages, 1)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 2)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_REQUIRES_MATCHING_AGENT,
      constantOf(messages, 3)
    );
    assertEquals(
      PLAN_EXPLAIN_DONE,
      messages.get(4)
    );
    assertEquals(5, messages.size());
  }

  /**
   * A simple task example with an agent constraint.
   *
   * @throws Exception On errors
   */

  @Test
  public void testTasks1()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(this.strings, "p", 1L);

    final var toolExec =
      new NPPlanToolExecution(
        NPToolReferenceName.of("texec"),
        NPToolExecutionIdentifier.of("te", 1L),
        Set.of()
      );

    planBuilder.addToolReference(new NPToolReference(
      NPToolReferenceName.of("texec"),
      NPToolName.of("arg"),
      Version.of(1, 0, 0)
    ));

    final var t0 =
      planBuilder.addTask("t0")
        .setToolExecution(toolExec);

    final var t1 =
      planBuilder.addTask("t1")
        .setToolExecution(toolExec);

    t1.addDependsOn(t0.name());
    t1.setAgentMustBeSameAs(t0);

    final var plan =
      planBuilder.build();

    final var explanation =
      NPPlanExplanation.explain(this.strings, plan);

    final var messages =
      this.dumpMessages(explanation);

    assertEquals(
      PLAN_EXPLAIN_TASK_BECOMES_READY_EMPTY,
      constantOf(messages, 0)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_REQUIRES_MATCHING_AGENT,
      constantOf(messages, 1)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 2)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_REQUIRES_SPECIFIC_AGENT,
      constantOf(messages, 3)
    );
    assertEquals(
      PLAN_EXPLAIN_DONE,
      messages.get(4)
    );
    assertEquals(5, messages.size());
  }

  /**
   * A simple task example.
   *
   * @throws Exception On errors
   */

  @Test
  public void testTasks2()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(this.strings, "p", 1L);

    final var toolExec =
      new NPPlanToolExecution(
        NPToolReferenceName.of("texec"),
        NPToolExecutionIdentifier.of("te", 1L),
        Set.of()
      );

    planBuilder.addToolReference(new NPToolReference(
      NPToolReferenceName.of("texec"),
      NPToolName.of("arg"),
      Version.of(1, 0, 0)
    ));

    final var t0 =
      planBuilder.addTask("t0")
        .setToolExecution(toolExec);

    final var t1 =
      planBuilder.addTask("t1")
        .setToolExecution(toolExec);

    t1.addDependsOn(t0.name());

    final var agent0 =
      NPAgentID.of("c170409e-ccf1-4c2b-99c0-bf77fc213c7a");
    final var agent1 =
      NPAgentID.of("6e034f18-a4ee-4161-8ce3-d86986064c65");

    final var plan =
      planBuilder.build();

    final var explanation =
      NPPlanExplanation.explain(this.strings, plan);

    final var messages =
      this.dumpMessages(explanation);

    assertEquals(
      PLAN_EXPLAIN_TASK_BECOMES_READY_EMPTY,
      constantOf(messages, 0)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_REQUIRES_MATCHING_AGENT,
      constantOf(messages, 1)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 2)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_REQUIRES_MATCHING_AGENT,
      constantOf(messages, 3)
    );
    assertEquals(
      PLAN_EXPLAIN_DONE,
      messages.get(4)
    );
    assertEquals(5, messages.size());
  }

  /**
   * A simple task example.
   *
   * @throws Exception On errors
   */

  @Test
  public void testTasksTimeouts0()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(this.strings, "p", 1L);

    final var toolExec =
      new NPPlanToolExecution(
        NPToolReferenceName.of("texec"),
        NPToolExecutionIdentifier.of("te", 1L),
        Set.of()
      );

    planBuilder.addToolReference(new NPToolReference(
      NPToolReferenceName.of("texec"),
      NPToolName.of("arg"),
      Version.of(1, 0, 0)
    ));

    final var t0 =
      planBuilder.addTask("t0")
        .setToolExecution(toolExec)
        .setExecutionTimeout(Duration.ofSeconds(3L))
        .setAgentSelectionTimeout(Duration.ofSeconds(5L));

    final var plan =
      planBuilder.build();

    final var explanation =
      NPPlanExplanation.explain(this.strings, plan);

    final var messages =
      this.dumpMessages(explanation);

    assertEquals(
      PLAN_EXPLAIN_TASK_BECOMES_READY_EMPTY,
      constantOf(messages, 0)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_REQUIRES_MATCHING_AGENT,
      constantOf(messages, 1)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_AGENT_TIMEOUT,
      constantOf(messages, 2)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_EXECUTION_TIMEOUT,
      constantOf(messages, 3)
    );
    assertEquals(
      PLAN_EXPLAIN_DONE,
      messages.get(4)
    );

    assertEquals(5, messages.size());
  }

  /**
   * A simple task example.
   *
   * @throws Exception On errors
   */

  @Test
  public void testTasksTimeouts1()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(this.strings, "p", 1L);

    final var toolExec =
      new NPPlanToolExecution(
        NPToolReferenceName.of("texec"),
        NPToolExecutionIdentifier.of("te", 1L),
        Set.of()
      );

    planBuilder.addToolReference(new NPToolReference(
      NPToolReferenceName.of("texec"),
      NPToolName.of("arg"),
      Version.of(1, 0, 0)
    ));

    final var t0 =
      planBuilder.addTask("t0")
        .setToolExecution(toolExec);

    final var t1 =
      planBuilder.addTask("t1")
        .setToolExecution(toolExec)
        .setAgentMustBeSameAs(t0)
        .setExecutionTimeout(Duration.ofSeconds(3L))
        .setAgentSelectionTimeout(Duration.ofSeconds(5L));

    final var plan =
      planBuilder.build();

    final var explanation =
      NPPlanExplanation.explain(this.strings, plan);

    final var messages =
      this.dumpMessages(explanation);

    assertEquals(
      PLAN_EXPLAIN_TASK_BECOMES_READY_EMPTY,
      constantOf(messages, 0)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_REQUIRES_MATCHING_AGENT,
      constantOf(messages, 1)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_BECOMES_READY_DEPENDENCIES,
      constantOf(messages, 2)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_REQUIRES_SPECIFIC_AGENT,
      constantOf(messages, 3)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_AGENT_TIMEOUT,
      constantOf(messages, 4)
    );
    assertEquals(
      PLAN_EXPLAIN_TASK_EXECUTION_TIMEOUT,
      constantOf(messages, 5)
    );
    assertEquals(
      PLAN_EXPLAIN_DONE,
      messages.get(6)
    );

    assertEquals(7, messages.size());
  }
}
