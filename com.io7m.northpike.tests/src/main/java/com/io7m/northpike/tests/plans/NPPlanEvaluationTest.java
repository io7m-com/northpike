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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.plans.NPPlanToolExecution;
import com.io7m.northpike.plans.NPPlanType;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluation;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusFailed;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusInProgress;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusSucceeded;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentAcceptedTask;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentReportedTaskFailure;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentReportedTaskSuccess;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.verona.core.Version;
import org.jgrapht.traverse.TopologicalOrderIterator;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

@Timeout(5L)
public final class NPPlanEvaluationTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPPlanEvaluationTest.class);

  private NPStrings strings;
  private ArrayList<NPPlanEvaluationEventType> events;
  private ArrayList<String> eventTexts;
  private NPFakeClock clock;

  @BeforeEach
  public void setup()
  {
    this.strings = NPStrings.create(Locale.ROOT);
    this.events = new ArrayList<>();
    this.eventTexts = new ArrayList<String>();
    this.clock = new NPFakeClock();
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
      NPPlans.builder(this.strings, new RDottedName("p"), 1L)
        .build();

    final var execution =
      NPPlanEvaluation.create(this.clock, plan);

    assertInstanceOf(StatusSucceeded.class, execution.step(List.of()));
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
      NPPlans.builder(this.strings, new RDottedName("p"), 1L);

    final var b0 =
      planBuilder.addBarrier(new RDottedName("b0"));
    final var b1 =
      planBuilder.addBarrier(new RDottedName("b1"));
    final var b2 =
      planBuilder.addBarrier(new RDottedName("b2"));

    b2.addDependsOn(b1.name());
    b1.addDependsOn(b0.name());

    final var plan =
      planBuilder.build();

    final var execution =
      NPPlanEvaluation.create(this.clock, plan);

    this.runPlanToTerminal(execution);

    assertEquals(
      List.of(
        "[ElementBecameReady b0]",
        "[ElementSucceeded b0]",
        "[ElementBecameReady b1]",
        "[ElementSucceeded b1]",
        "[ElementBecameReady b2]",
        "[ElementSucceeded b2]"
      ),
      this.eventTexts
    );
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
      NPPlans.builder(this.strings, new RDottedName("p"), 1L);

    final var b0_0 =
      planBuilder.addBarrier(new RDottedName("b0_0"));
    final var b0_1 =
      planBuilder.addBarrier(new RDottedName("b0_1"));
    final var b0_2 =
      planBuilder.addBarrier(new RDottedName("b0_2"));

    b0_2.addDependsOn(b0_1.name());
    b0_1.addDependsOn(b0_0.name());

    final var b1_0 =
      planBuilder.addBarrier(new RDottedName("b1_0"));
    final var b1_1 =
      planBuilder.addBarrier(new RDottedName("b1_1"));
    final var b1_2 =
      planBuilder.addBarrier(new RDottedName("b1_2"));

    b1_2.addDependsOn(b1_1.name());
    b1_1.addDependsOn(b1_0.name());

    final var b2_0 =
      planBuilder.addBarrier(new RDottedName("b2_0"));
    final var b2_1 =
      planBuilder.addBarrier(new RDottedName("b2_1"));
    final var b2_2 =
      planBuilder.addBarrier(new RDottedName("b2_2"));

    b2_2.addDependsOn(b2_1.name());
    b2_1.addDependsOn(b2_0.name());

    final var b_end =
      planBuilder.addBarrier(new RDottedName("b_end"));

    b_end.addDependsOn(b0_2.name());
    b_end.addDependsOn(b1_2.name());
    b_end.addDependsOn(b2_2.name());

    final var plan =
      planBuilder.build();

    dot(plan);

    final var execution =
      NPPlanEvaluation.create(this.clock, plan);

    this.runPlanToTerminal(execution);

    assertEquals(
      List.of(
        "[ElementBecameReady b0_0]",
        "[ElementBecameReady b1_0]",
        "[ElementBecameReady b2_0]",
        "[ElementSucceeded b0_0]",
        "[ElementSucceeded b1_0]",
        "[ElementSucceeded b2_0]",

        "[ElementBecameReady b0_1]",
        "[ElementBecameReady b1_1]",
        "[ElementBecameReady b2_1]",
        "[ElementSucceeded b0_1]",
        "[ElementSucceeded b1_1]",
        "[ElementSucceeded b2_1]",

        "[ElementBecameReady b0_2]",
        "[ElementBecameReady b1_2]",
        "[ElementBecameReady b2_2]",
        "[ElementSucceeded b0_2]",
        "[ElementSucceeded b1_2]",
        "[ElementSucceeded b2_2]",

        "[ElementBecameReady b_end]",
        "[ElementSucceeded b_end]"
      ),
      this.eventTexts
    );
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
      NPPlans.builder(this.strings, new RDottedName("p"), 1L);

    final var toolExec =
      new NPPlanToolExecution(
        new RDottedName("texec"),
        new RDottedName("arg"),
        Set.of()
      );

    planBuilder.addToolReference(new NPToolReference(
      new RDottedName("texec"),
      new RDottedName("arg"),
      Version.of(1, 0, 0)
    ));

    final var t0 =
      planBuilder.addTask(new RDottedName("t0"))
        .setToolExecution(toolExec);

    final var t1 =
      planBuilder.addTask(new RDottedName("t1"))
        .setToolExecution(toolExec);

    t1.addDependsOn(t0.name());

    final var agent0 =
      new NPAgentID(UUID.fromString("c170409e-ccf1-4c2b-99c0-bf77fc213c7a"));
    final var agent1 =
      new NPAgentID(UUID.fromString("6e034f18-a4ee-4161-8ce3-d86986064c65"));

    final var plan =
      planBuilder.build();

    final var execution =
      NPPlanEvaluation.create(this.clock, plan);

    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));
    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));

    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(new AgentAcceptedTask(t0.name(), agent0)))
      ));
    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(new AgentReportedTaskSuccess(t0.name(), agent0)))
      ));
    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));

    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(new AgentAcceptedTask(t1.name(), agent1)))
      ));
    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(new AgentReportedTaskSuccess(t1.name(), agent1)))
      ));
    this.recordEvents(
      assertInstanceOf(StatusSucceeded.class, execution.step(List.of())));

    assertEquals(
      List.of(
        "[ElementBecameReady t0]",
        "[TaskRequiresMatchingAgent t0]",
        "[ElementSucceeded t0]",
        "[ElementBecameReady t1]",
        "[TaskRequiresMatchingAgent t1]",
        "[ElementSucceeded t1]"
      ),
      this.eventTexts
    );
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
      NPPlans.builder(this.strings, new RDottedName("p"), 1L);

    final var toolExec =
      new NPPlanToolExecution(
        new RDottedName("texec"),
        new RDottedName("arg"),
        Set.of()
      );

    planBuilder.addToolReference(new NPToolReference(
      new RDottedName("texec"),
      new RDottedName("arg"),
      Version.of(1, 0, 0)
    ));

    final var t0 =
      planBuilder.addTask(new RDottedName("t0"))
        .setToolExecution(toolExec);

    final var t1 =
      planBuilder.addTask(new RDottedName("t1"))
        .setToolExecution(toolExec);

    t1.addDependsOn(t0.name());
    t1.setAgentMustBeSameAs(t0);

    final var agent0 =
      new NPAgentID(UUID.fromString("c170409e-ccf1-4c2b-99c0-bf77fc213c7a"));

    final var plan =
      planBuilder.build();

    final var execution =
      NPPlanEvaluation.create(this.clock, plan);

    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));
    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));

    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(new AgentAcceptedTask(t0.name(), agent0)))
      ));
    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(new AgentReportedTaskSuccess(t0.name(), agent0)))
      ));
    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));

    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(new AgentAcceptedTask(t1.name(), agent0)))
      ));
    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(new AgentReportedTaskSuccess(t1.name(), agent0)))
      ));
    this.recordEvents(
      assertInstanceOf(StatusSucceeded.class, execution.step(List.of())));

    assertEquals(
      List.of(
        "[ElementBecameReady t0]",
        "[TaskRequiresMatchingAgent t0]",
        "[ElementSucceeded t0]",
        "[ElementBecameReady t1]",
        "[TaskRequiresSpecificAgent t1 c170409e-ccf1-4c2b-99c0-bf77fc213c7a]",
        "[ElementSucceeded t1]"
      ),
      this.eventTexts
    );
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
      NPPlans.builder(this.strings, new RDottedName("p"), 1L);

    final var toolExec =
      new NPPlanToolExecution(
        new RDottedName("texec"),
        new RDottedName("arg"),
        Set.of()
      );

    planBuilder.addToolReference(new NPToolReference(
      new RDottedName("texec"),
      new RDottedName("arg"),
      Version.of(1, 0, 0)
    ));

    final var t0 =
      planBuilder.addTask(new RDottedName("t0"))
        .setToolExecution(toolExec);

    final var t1 =
      planBuilder.addTask(new RDottedName("t1"))
        .setToolExecution(toolExec);

    t1.addDependsOn(t0.name());

    final var agent0 =
      new NPAgentID(UUID.fromString("c170409e-ccf1-4c2b-99c0-bf77fc213c7a"));
    final var agent1 =
      new NPAgentID(UUID.fromString("6e034f18-a4ee-4161-8ce3-d86986064c65"));

    final var plan =
      planBuilder.build();

    final var execution =
      NPPlanEvaluation.create(this.clock, plan);

    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));
    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));

    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(new AgentAcceptedTask(t0.name(), agent0)))
      ));
    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(new AgentReportedTaskFailure(t0.name(), agent0)))
      ));
    this.recordEvents(
      assertInstanceOf(StatusFailed.class, execution.step(List.of())));

    assertEquals(
      List.of(
        "[ElementBecameReady t0]",
        "[TaskRequiresMatchingAgent t0]",
        "[ElementFailed t0]"
      ),
      this.eventTexts
    );
  }

  /**
   * Tasks can time out waiting for agents, if required.
   *
   * @throws Exception On errors
   */

  @Test
  public void testTaskAgentTimeout()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(this.strings, new RDottedName("p"), 1L);

    final var toolExec =
      new NPPlanToolExecution(
        new RDottedName("texec"),
        new RDottedName("arg"),
        Set.of()
      );

    planBuilder.addToolReference(new NPToolReference(
      new RDottedName("texec"),
      new RDottedName("arg"),
      Version.of(1, 0, 0)
    ));

    final var t0 =
      planBuilder.addTask(new RDottedName("t0"))
        .setToolExecution(toolExec)
        .setAgentAssignmentTimeout(Duration.ofSeconds(2L));

    final var plan =
      planBuilder.build();

    final var execution =
      NPPlanEvaluation.create(this.clock, plan);

    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));
    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));
    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));

    this.clock.timeNow =
      this.clock.timeNow.plusSeconds(3L);

    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));
    this.recordEvents(
      assertInstanceOf(StatusFailed.class, execution.step(List.of())));

    assertEquals(
      List.of(
        "[ElementBecameReady t0]",
        "[TaskRequiresMatchingAgent t0]",
        "[TaskRequiresMatchingAgent t0]",
        "[TaskAgentAssignmentTimedOut t0]",
        "[ElementFailed t0]"
      ),
      this.eventTexts
    );
  }

  /**
   * Tasks can time out executing, if required.
   *
   * @throws Exception On errors
   */

  @Test
  public void testTaskExecutionTimeout()
    throws Exception
  {
    final var planBuilder =
      NPPlans.builder(this.strings, new RDottedName("p"), 1L);

    final var toolExec =
      new NPPlanToolExecution(
        new RDottedName("texec"),
        new RDottedName("arg"),
        Set.of()
      );

    planBuilder.addToolReference(new NPToolReference(
      new RDottedName("texec"),
      new RDottedName("arg"),
      Version.of(1, 0, 0)
    ));

    final var t0 =
      planBuilder.addTask(new RDottedName("t0"))
        .setToolExecution(toolExec)
        .setExecutionTimeout(Duration.ofSeconds(2L));

    final var plan =
      planBuilder.build();

    final var execution =
      NPPlanEvaluation.create(this.clock, plan);

    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));
    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));

    final var agent =
      new NPAgentID(UUID.fromString("c170409e-ccf1-4c2b-99c0-bf77fc213c7a"));

    this.recordEvents(
      assertInstanceOf(
        StatusInProgress.class,
        execution.step(List.of(
          new AgentAcceptedTask(t0.name(), agent)
        ))
      ));

    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));

    this.clock.timeNow =
      this.clock.timeNow.plusSeconds(3L);

    this.recordEvents(
      assertInstanceOf(StatusInProgress.class, execution.step(List.of())));
    this.recordEvents(
      assertInstanceOf(StatusFailed.class, execution.step(List.of())));

    assertEquals(
      List.of(
        "[ElementBecameReady t0]",
        "[TaskRequiresMatchingAgent t0]",
        "[TaskExecutionTimedOut t0]",
        "[ElementFailed t0]"
      ),
      this.eventTexts
    );
  }

  private void runPlanToTerminal(
    final NPPlanEvaluationType execution)
  {
    for (int index = 0; index < 1000; ++index) {
      final var e = execution.step(List.of());
      this.recordEvents(e);
      if (e.isTerminal()) {
        break;
      }
    }

    final var e = execution.step(List.of());
    assertTrue(e.isTerminal(), "Evaluation must have completed.");
  }

  private void recordEvents(
    final NPPlanEvaluationStatusType s)
  {
    for (final var e : s.events()) {
      LOG.debug("event: {}", e);
      this.events.add(e);
      this.eventTexts.add(e.toString());
    }
  }

  private static void dot(
    final NPPlanType plan)
  {
    final var graph =
      plan.graph();

    final var topo = new TopologicalOrderIterator<>(graph);
    System.out.println("digraph g {");

    while (topo.hasNext()) {
      final var next =
        topo.next();
      final var dependencies =
        next.dependsOn();

      for (final var dependency : dependencies) {
        System.out.printf(
          "  %s -> %s;%n",
          dependency,
          next.name()
        );
      }
    }

    System.out.println("}");
  }
}
