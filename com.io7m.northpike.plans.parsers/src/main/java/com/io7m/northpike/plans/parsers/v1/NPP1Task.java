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


package com.io7m.northpike.plans.parsers.v1;

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.blackthorne.core.Blackthorne;
import com.io7m.northpike.model.agents.NPAgentResourceName;
import com.io7m.northpike.model.NPFailurePolicyType;
import com.io7m.northpike.model.NPFailureRetry;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.model.plans.NPPlanElementDescriptionType;
import com.io7m.northpike.model.plans.NPPlanElementName;
import com.io7m.northpike.model.plans.NPPlanTaskDescription;
import com.io7m.northpike.model.plans.NPPlanToolExecution;
import org.xml.sax.Attributes;

import java.time.Duration;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static com.io7m.northpike.model.NPFailureFail.FAIL;
import static com.io7m.northpike.model.NPFailureIgnore.IGNORE_FAILURE;
import static com.io7m.northpike.plans.parsers.v1.NPP1.element;

/**
 * A task parser.
 */

public final class NPP1Task
  implements BTElementHandlerType<Object, NPPlanElementDescriptionType>
{
  private NPPlanElementName name;
  private String description;

  private NPP1AgentRequireWithLabelsMatchingExpression requireWithLabels =
    new NPP1AgentRequireWithLabelsMatchingExpression(
      new NPComparisonSetType.Anything<>()
    );

  private NPP1AgentPreferWithLabelsMatchingExpression preferWithLabels =
    new NPP1AgentPreferWithLabelsMatchingExpression(
      new NPComparisonSetType.Anything<>()
    );

  private Optional<NPP1AgentRequireSameAsUsedFor> sameAsUsedFor =
    Optional.empty();

  private Optional<Duration> agentSelectionTimeout =
    Optional.empty();

  private Optional<Duration> executionTimeout =
    Optional.empty();

  private Set<NPAgentResourceName> lockAgentResources =
    new TreeSet<>();

  private NPPlanToolExecution toolExecution;

  private Set<NPPlanElementName> dependsOn =
    new TreeSet<>();

  private NPFailurePolicyType failurePolicy =
    FAIL;

  /**
   * A task parser.
   *
   * @param context The parse context
   */

  public NPP1Task(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ?>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      Map.entry(
        element("AgentRequireWithLabelsMatching"),
        NPP1AgentRequireWithLabelsMatching::new
      ),
      Map.entry(
        element("AgentPreferWithLabelsMatching"),
        NPP1AgentPreferWithLabelsMatching::new
      ),
      Map.entry(
        element("AgentRequireSameAsUsedFor"),
        NPP1AgentRequireSameAsUsedFor.handler()
      ),
      Map.entry(
        element("ToolExecution"),
        NPP1Handlers.toolExecution()
      ),
      Map.entry(
        element("AgentLockResources"),
        NPP1AgentLockResources::new
      ),
      Map.entry(
        element("DependsOn"),
        Blackthorne.forScalarAttribute(
          element("DependsOn"),
          (c, a) -> new NPP1DependsOn(NPPlanElementName.of(a.getValue("Task")))
        )
      ),
      Map.entry(
        element("FailurePolicyFail"),
        Blackthorne.forScalarAttribute(
          element("FailurePolicyFail"),
          (c, a) -> FAIL
        )
      ),
      Map.entry(
        element("FailurePolicyIgnore"),
        Blackthorne.forScalarAttribute(
          element("FailurePolicyIgnore"),
          (c, a) -> IGNORE_FAILURE
        )
      ),
      Map.entry(
        element("FailurePolicyRetry"),
        Blackthorne.forScalarAttribute(
          element("FailurePolicyRetry"),
          (c, a) -> new NPFailureRetry(
            Integer.parseUnsignedInt(a.getValue("RetryCount"))
          )
        )
      )
    );
  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.name =
      NPPlanElementName.of(attributes.getValue("Name"));
    this.description =
      attributes.getValue("Description");

    this.executionTimeout =
      Optional.ofNullable(attributes.getValue("ExecutionTimeout"))
        .map(Duration::parse);

    this.agentSelectionTimeout =
      Optional.ofNullable(attributes.getValue("AgentSelectionTimeout"))
        .map(Duration::parse);
  }

  @Override
  public NPPlanElementDescriptionType onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPPlanTaskDescription(
      this.name,
      this.description,
      this.requireWithLabels.match(),
      this.preferWithLabels.match(),
      this.sameAsUsedFor.map(NPP1AgentRequireSameAsUsedFor::name),
      this.agentSelectionTimeout,
      this.executionTimeout,
      this.lockAgentResources,
      this.toolExecution,
      this.dependsOn,
      this.failurePolicy
    );
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final Object result)
  {
    if (result instanceof final NPP1AgentRequireWithLabelsMatchingExpression e) {
      this.requireWithLabels = e;
      return;
    }
    if (result instanceof final NPP1AgentPreferWithLabelsMatchingExpression e) {
      this.preferWithLabels = e;
      return;
    }
    if (result instanceof final NPP1AgentRequireSameAsUsedFor e) {
      this.sameAsUsedFor = Optional.of(e);
      return;
    }
    if (result instanceof final NPPlanToolExecution e) {
      this.toolExecution = e;
      return;
    }
    if (result instanceof final NPP1AgentLockResourcesExpression e) {
      this.lockAgentResources.addAll(e.resources());
      return;
    }
    if (result instanceof final NPP1DependsOn e) {
      this.dependsOn.add(e.task());
      return;
    }
    if (result instanceof final NPFailurePolicyType e) {
      this.failurePolicy = e;
      return;
    }

    throw new IllegalStateException(
      "Unrecognized result: %s".formatted(result)
    );
  }
}
