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
import com.io7m.northpike.model.NPAgentLabelMatchType.Specific;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.plans.NPPlanBarrierType;
import com.io7m.northpike.plans.NPPlanElementName;
import com.io7m.northpike.plans.NPPlanException;
import com.io7m.northpike.plans.NPPlanName;
import com.io7m.northpike.plans.NPPlanTaskType;
import com.io7m.northpike.plans.NPPlanToolExecution;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.verona.core.Version;
import org.jgrapht.traverse.TopologicalOrderIterator;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorApiMisuse;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorCyclic;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorDuplicate;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class NPPlansTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPPlansTest.class);

  private NPStrings strings;

  @BeforeEach
  public void setup()
  {
    this.strings = NPStrings.create(Locale.ROOT);
  }

  /**
   * Empty plans are empty.
   *
   * @throws Exception On errors
   */

  @Test
  public void testPlanEmpty()
    throws Exception
  {
    final var plan =
      NPPlans.builder(this.strings, "p", 1L)
        .build();

    assertEquals(NPPlanName.of("p"), plan.name());
    assertEquals(1L, plan.version());
    assertEquals(Map.of(), plan.elements());
    assertEquals(Map.of(), plan.toolReferences());
  }

  /**
   * Duplicate tool references are disallowed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testDuplicateToolReference()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    builder.addToolReference(
      new NPToolReference(
        new RDottedName("x"),
        new RDottedName("y"),
        Version.of(1, 0, 0)
      )
    );

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        builder.addToolReference(
          new NPToolReference(
            new RDottedName("x"),
            new RDottedName("y"),
            Version.of(1, 0, 0)
          )
        );
      });

    assertEquals(errorDuplicate(), ex.errorCode());
  }

  /**
   * Duplicate barriers are disallowed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testDuplicateBarriers()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    builder.addBarrier("x");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        builder.addBarrier("x");
      });

    assertEquals(errorDuplicate(), ex.errorCode());
  }

  /**
   * Duplicate tasks are disallowed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testDuplicateTasks()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    builder.addTask("x");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        builder.addTask("x");
      });

    assertEquals(errorDuplicate(), ex.errorCode());
  }

  /**
   * Duplicate tasks are disallowed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testDuplicateBarrierTask()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    builder.addBarrier("x");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        builder.addTask("x");
      });

    assertEquals(errorDuplicate(), ex.errorCode());
  }

  /**
   * Duplicate barriers are disallowed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testDuplicateTaskBarrier()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    builder.addTask("x");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        builder.addBarrier("x");
      });

    assertEquals(errorDuplicate(), ex.errorCode());
  }

  /**
   * Circular dependencies are disallowed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testDependencyCyclicBarrier0()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    final var b0 =
      builder.addBarrier("x");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        b0.addDependsOn("x");
      });

    assertEquals(errorCyclic(), ex.errorCode());
  }

  /**
   * Circular dependencies are disallowed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testDependencyCyclicBarrier1()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    final var b0 =
      builder.addBarrier("x");
    final var b1 =
      builder.addBarrier("y");

    b0.addDependsOn("y");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        b1.addDependsOn("x");
      });

    assertEquals(errorCyclic(), ex.errorCode());
  }

  /**
   * Circular dependencies are disallowed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testDependencyCyclicTask0()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    final var b0 =
      builder.addTask("x");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        b0.addDependsOn("x");
      });

    assertEquals(errorCyclic(), ex.errorCode());
  }

  /**
   * Circular dependencies are disallowed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testDependencyCyclicTask1()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    final var b0 =
      builder.addTask("x");
    final var b1 =
      builder.addTask("y");

    b0.addDependsOn("y");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        b1.addDependsOn("x");
      });

    assertEquals(errorCyclic(), ex.errorCode());
  }

  /**
   * Nonexistent dependencies are disallowed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testDependencyNonexistent0()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    final var barrierBuilder =
      builder.addBarrier("x");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        barrierBuilder.addDependsOn("y");
      });

    assertEquals(errorNonexistent(), ex.errorCode());
  }

  /**
   * A single task plan has the expected values.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSingleTask()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    final var t0 = new NPToolReference(
      new RDottedName("t0"),
      new RDottedName("tk0"),
      Version.of(1, 0, 0)
    );

    builder.addToolReference(t0);

    final var t1 = new NPToolReference(
      new RDottedName("t1"),
      new RDottedName("tk1"),
      Version.of(1, 0, 0)
    );

    builder.addToolReference(t1);

    final var b0 =
      builder.addTask("x");

    final var toolExecution =
      new NPPlanToolExecution(
        new RDottedName("t0"),
        NPToolExecutionIdentifier.of("ta", 1L),
        Set.of(new RDottedName("t1"))
      );

    b0.addLockAgentResource(new RDottedName("r0"))
      .addLockAgentResource(new RDottedName("r1"))
      .addLockAgentResource(new RDottedName("r2"))
      .setAgentPreferWithLabels(new Specific(new RDottedName("x")))
      .setAgentRequireWithLabels(new Specific(new RDottedName("y")))
      .setDescription("A task.")
      .setToolExecution(toolExecution);

    final var p = builder.build();
    assertEquals(t0, p.toolReferences().get(t0.name()));
    assertEquals(t1, p.toolReferences().get(t1.name()));

    final var t =
      assertInstanceOf(
        NPPlanTaskType.class,
        p.elements().get(NPPlanElementName.of("x"))
      );

    assertEquals("A task.", t.description());
    assertEquals(NPPlanElementName.of("x"), t.name());
    assertEquals(new Specific(new RDottedName("x")), t.agentPreferWithLabel());
    assertEquals(new Specific(new RDottedName("y")), t.agentRequireWithLabel());
    assertEquals(Set.of(
      new RDottedName("r0"),
      new RDottedName("r1"),
      new RDottedName("r2")
    ), t.lockAgentResources());
    assertEquals(List.of(), t.dependsOn());
    assertEquals(toolExecution, t.toolExecution());

    new TopologicalOrderIterator<>(p.graph())
      .forEachRemaining(e -> LOG.debug("{}", e));
  }

  /**
   * A single barrier plan has the expected values.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSingleBarrier()
    throws Exception
  {
    final var builder =
      NPPlans.builder(
        this.strings,
        NPPlanName.of("single-barrier"),
        1L
      );

    final var b0 =
      builder.addBarrier("x");

    b0.setDescription("A barrier.");

    final var p = builder.build();
    final var t =
      assertInstanceOf(
        NPPlanBarrierType.class,
        p.elements().get(NPPlanElementName.of("x"))
      );

    assertEquals("A barrier.", t.description());
    assertEquals(NPPlanElementName.of("x"), t.name());
    assertEquals(List.of(), t.dependsOn());

    new TopologicalOrderIterator<>(p.graph())
      .forEachRemaining(e -> LOG.debug("{}", e));

    assertTrue(p.toString().contains("single-barrier"));
    assertTrue(p.toString().contains("1"));
  }

  /**
   * A three barrier plan has the expected values.
   *
   * @throws Exception On errors
   */

  @Test
  public void testThreeBarrier()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    final var b0 =
      builder.addBarrier("x");
    final var b1 =
      builder.addBarrier("y");
    final var b2 =
      builder.addBarrier("z");

    b2.addDependsOn(b1.name());
    b1.addDependsOn(b0.name());

    final var p = builder.build();
    final var t0 =
      assertInstanceOf(
        NPPlanBarrierType.class,
        p.elements().get(NPPlanElementName.of("x"))
      );
    final var t1 =
      assertInstanceOf(
        NPPlanBarrierType.class,
        p.elements().get(NPPlanElementName.of("y"))
      );
    final var t2 =
      assertInstanceOf(
        NPPlanBarrierType.class,
        p.elements().get(NPPlanElementName.of("z"))
      );

    assertEquals(List.of(), t0.dependsOn());
    assertEquals(List.of(NPPlanElementName.of("x")), t1.dependsOn());
    assertEquals(List.of(NPPlanElementName.of("y")), t2.dependsOn());

    new TopologicalOrderIterator<>(p.graph())
      .forEachRemaining(e -> LOG.debug("{}", e));
  }

  /**
   * Tool executions are required.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecutionRequired0()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    builder.addTask("x");

    final var ex =
      assertThrows(NPPlanException.class, builder::build);

    assertEquals(errorApiMisuse(), ex.errorCode());
  }

  /**
   * Tool executions must refer to tools that exist.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecutionNonexistent0()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    final var b0 =
      builder.addTask("x");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        b0.setToolExecution(new NPPlanToolExecution(
          new RDottedName("t"),
          NPToolExecutionIdentifier.of("y", 1L),
          Set.of()
        ));
      });

    assertEquals(errorNonexistent(), ex.errorCode());
  }

  /**
   * Tool executions must refer to tools that exist.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecutionNonexistent1()
    throws Exception
  {
    final var builder =
      NPPlans.builder(this.strings, "p", 1L);

    builder.addToolReference(
      new NPToolReference(
        new RDottedName("t"),
        new RDottedName("t0"),
        Version.of(1,0,0))
    );

    final var b0 =
      builder.addTask("x");

    final var ex =
      assertThrows(NPPlanException.class, () -> {
        b0.setToolExecution(new NPPlanToolExecution(
          new RDottedName("t"),
          NPToolExecutionIdentifier.of("y", 1L),
          Set.of(new RDottedName("k"))
        ));
      });

    assertEquals(errorNonexistent(), ex.errorCode());
  }
}
