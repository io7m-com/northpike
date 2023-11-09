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

import com.io7m.northpike.model.NPCleanImmediately;
import com.io7m.northpike.model.NPCleanLater;
import com.io7m.northpike.model.NPCleanPolicyType;
import com.io7m.northpike.model.NPFailureFail;
import com.io7m.northpike.model.NPFailureIgnore;
import com.io7m.northpike.model.NPFailurePolicyType;
import com.io7m.northpike.model.NPFailureRetry;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import com.io7m.northpike.model.agents.NPAgentResourceName;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.Anything;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsEqualTo;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsNotEqualTo;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsOverlapping;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsSubsetOf;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsSupersetOf;
import com.io7m.northpike.model.plans.NPPlanBarrierType;
import com.io7m.northpike.model.plans.NPPlanElementName;
import com.io7m.northpike.model.plans.NPPlanElementType;
import com.io7m.northpike.model.plans.NPPlanTaskType;
import com.io7m.northpike.model.plans.NPPlanTimeouts;
import com.io7m.northpike.model.plans.NPPlanToolExecution;
import com.io7m.northpike.model.plans.NPPlanType;
import com.io7m.northpike.plans.parsers.NPPlanSchemas;
import org.jgrapht.traverse.TopologicalOrderIterator;

import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A serializer for plans (v1) data.
 */

public final class NPP1Serializer
{
  private final XMLOutputFactory outputs;
  private final XMLStreamWriter output;
  private final String ns;

  private NPP1Serializer(
    final OutputStream outputStream)
    throws XMLStreamException
  {
    this.outputs =
      XMLOutputFactory.newFactory();
    this.output =
      this.outputs.createXMLStreamWriter(outputStream, "UTF-8");
    this.ns =
      NPPlanSchemas.plans1().namespace().toString();
  }

  /**
   * A serializer for plans (v1) data.
   *
   * @param outputStream The output stream
   *
   * @return A serializer
   *
   * @throws XMLStreamException On errors
   */

  public static NPP1Serializer create(
    final OutputStream outputStream)
    throws XMLStreamException
  {
    return new NPP1Serializer(outputStream);
  }

  /**
   * Execute the serializer.
   *
   * @param plan The input plan
   *
   * @throws XMLStreamException On errors
   */

  public void serialize(
    final NPPlanType plan)
    throws XMLStreamException
  {
    this.output.writeStartDocument("UTF-8", "1.0");
    this.serializePlan(plan);
    this.output.writeEndDocument();
  }

  private void serializePlan(
    final NPPlanType plan)
    throws XMLStreamException
  {
    this.output.writeStartElement("Plan");
    this.output.writeDefaultNamespace(this.ns);

    this.output.writeAttribute(
      "Name",
      plan.identifier().name().toString()
    );
    this.output.writeAttribute(
      "Description",
      plan.description()
    );
    this.output.writeAttribute(
      "Version",
      Long.toUnsignedString(plan.identifier().version())
    );

    this.serializeTimeouts(plan.timeouts());

    final var tools = plan.toolReferences();
    if (!tools.isEmpty()) {
      this.serializeTools(tools);
    }

    final var graph =
      plan.graph();
    final var iterator =
      new TopologicalOrderIterator<>(graph);

    while (iterator.hasNext()) {
      this.serializePlanElement(iterator.next());
    }

    this.output.writeEndElement();
  }

  private void serializeTimeouts(
    final NPPlanTimeouts timeouts)
    throws XMLStreamException
  {
    this.output.writeStartElement("Timeouts");
    this.output.writeAttribute(
      "AgentSelection",
      timeouts.agentSelection().toString()
    );
    this.output.writeAttribute(
      "TaskExecution",
      timeouts.taskExecution().toString()
    );
    this.output.writeEndElement();
  }

  private void serializePlanElement(
    final NPPlanElementType element)
    throws XMLStreamException
  {
    switch (element) {
      case final NPPlanBarrierType barrier -> {
        this.serializePlanBarrier(barrier);
      }
      case final NPPlanTaskType task -> {
        this.serializePlanTask(task);
      }
    }
  }

  private void serializePlanTask(
    final NPPlanTaskType task)
    throws XMLStreamException
  {
    this.output.writeStartElement("Task");

    final var etOpt = task.executionTimeout();
    if (etOpt.isPresent()) {
      this.output.writeAttribute(
        "ExecutionTimeout",
        etOpt.get().toString()
      );
    }

    final var asOpt = task.agentSelectionTimeout();
    if (asOpt.isPresent()) {
      this.output.writeAttribute(
        "AgentSelectionTimeout",
        asOpt.get().toString()
      );
    }

    this.serializePlanElementCommon(task);
    this.serializePlanTaskAgentRequire(task);
    this.serializePlanTaskAgentPrefer(task);
    this.serializePlanTaskAgentLockResources(task.lockAgentResources());
    this.serializeCleanPolicy(task.cleanPolicy());
    this.serializeDependsOn(task.dependsOn());
    this.serializeFailurePolicy(task.failurePolicy());
    this.serializeToolExecution(task.toolExecution());
    this.output.writeEndElement();
  }

  private void serializeCleanPolicy(
    final NPCleanPolicyType cleanPolicy)
    throws XMLStreamException
  {
    switch (cleanPolicy) {
      case final NPCleanImmediately c -> {
        this.output.writeEmptyElement("CleanPolicyImmediately");
        return;
      }
      case final NPCleanLater c -> {
        this.output.writeEmptyElement("CleanPolicyLater");
        return;
      }
    }
  }

  private void serializeFailurePolicy(
    final NPFailurePolicyType failurePolicy)
    throws XMLStreamException
  {
    switch (failurePolicy) {
      case final NPFailureFail f -> {
        this.output.writeEmptyElement("FailurePolicyFail");
        return;
      }
      case final NPFailureIgnore f -> {
        this.output.writeEmptyElement("FailurePolicyIgnore");
        return;
      }
      case final NPFailureRetry retry -> {
        this.output.writeStartElement("FailurePolicyRetry");
        this.output.writeAttribute(
          "RetryCount",
          Integer.toUnsignedString(retry.retryCount()));
        this.output.writeEndElement();
        return;
      }
    }
  }

  private void serializeToolExecution(
    final NPPlanToolExecution execution)
    throws XMLStreamException
  {
    this.output.writeStartElement("ToolExecution");
    this.output.writeAttribute(
      "ReferenceName",
      execution.name().toString()
    );
    this.output.writeAttribute(
      "ExecutionName",
      execution.execution().name().toString()
    );
    this.output.writeAttribute(
      "ExecutionVersion",
      Long.toUnsignedString(execution.execution().version())
    );

    for (final var requirement : execution.toolRequirements()) {
      this.output.writeStartElement("ToolRequirement");
      this.output.writeAttribute("ReferenceName", requirement.toString());
      this.output.writeEndElement();
    }
    this.output.writeEndElement();
  }

  private void serializeDependsOn(
    final List<NPPlanElementName> names)
    throws XMLStreamException
  {
    final var namesSorted = new ArrayList<>(names);
    Collections.sort(namesSorted);

    for (final var name : namesSorted) {
      this.output.writeStartElement("DependsOn");
      this.output.writeAttribute("Task", name.toString());
      this.output.writeEndElement();
    }
  }

  private void serializePlanTaskAgentLockResources(
    final Set<NPAgentResourceName> names)
    throws XMLStreamException
  {
    this.output.writeStartElement("AgentLockResources");

    final var namesSorted = new ArrayList<>(names);
    Collections.sort(namesSorted);

    for (final var name : namesSorted) {
      this.output.writeStartElement("Resource");
      this.output.writeAttribute("Name", name.toString());
      this.output.writeEndElement();
    }

    this.output.writeEndElement();
  }

  private void serializePlanTaskAgentPrefer(
    final NPPlanTaskType task)
    throws XMLStreamException
  {
    this.output.writeStartElement("AgentPreferWithLabelsMatching");
    this.serializeSetComparison(task.agentPreferWithLabel());
    this.output.writeEndElement();
  }

  private void serializeSetComparison(
    final NPComparisonSetType<NPAgentLabelName> comparison)
    throws XMLStreamException
  {
    switch (comparison) {
      case final Anything<NPAgentLabelName> e -> {
        this.output.writeEmptyElement("SetIsAnything");
      }
      case final IsOverlapping<NPAgentLabelName> e -> {
        this.output.writeStartElement("SetIsOverlapping");
        for (final var ee : e.value()) {
          this.serializeSetElement(ee);
        }
        this.output.writeEndElement();
      }
      case final IsSupersetOf<NPAgentLabelName> e -> {
        this.output.writeStartElement("SetIsSupersetOf");
        for (final var ee : e.value()) {
          this.serializeSetElement(ee);
        }
        this.output.writeEndElement();
      }
      case final IsSubsetOf<NPAgentLabelName> e -> {
        this.output.writeStartElement("SetIsSubsetOf");
        for (final var ee : e.value()) {
          this.serializeSetElement(ee);
        }
        this.output.writeEndElement();
      }
      case final IsEqualTo<NPAgentLabelName> e -> {
        this.output.writeStartElement("SetIsEqualTo");
        for (final var ee : e.value()) {
          this.serializeSetElement(ee);
        }
        this.output.writeEndElement();
      }
      case final IsNotEqualTo<NPAgentLabelName> e -> {
        this.output.writeStartElement("SetIsNotEqualTo");
        for (final var ee : e.value()) {
          this.serializeSetElement(ee);
        }
        this.output.writeEndElement();
      }
    }
  }

  private void serializeSetElement(
    final NPAgentLabelName ee)
    throws XMLStreamException
  {
    this.output.writeStartElement("SetElement");
    this.output.writeAttribute("Value", ee.toString());
    this.output.writeEndElement();
  }

  private void serializePlanTaskAgentRequire(
    final NPPlanTaskType task)
    throws XMLStreamException
  {
    final var sameAsOpt = task.agentMustBeSameAs();
    if (sameAsOpt.isPresent()) {
      final var sameAs = sameAsOpt.get();
      this.output.writeStartElement("AgentRequireSameAsUsedFor");
      this.output.writeAttribute("Task", sameAs.name().toString());
      this.output.writeEndElement();
      return;
    }

    this.output.writeStartElement("AgentRequireWithLabelsMatching");
    this.serializeSetComparison(task.agentRequireWithLabel());
    this.output.writeEndElement();
  }

  private void serializePlanElementCommon(
    final NPPlanElementType element)
    throws XMLStreamException
  {
    this.output.writeAttribute(
      "Name", element.name().toString()
    );
    this.output.writeAttribute(
      "Description", element.description()
    );
  }

  private void serializePlanBarrier(
    final NPPlanBarrierType barrier)
    throws XMLStreamException
  {
    this.output.writeStartElement("Barrier");
    this.serializePlanElementCommon(barrier);
    this.serializeDependsOn(barrier.dependsOn());
    this.output.writeEndElement();
  }

  private void serializeTools(
    final Map<NPToolReferenceName, NPToolReference> tools)
    throws XMLStreamException
  {
    final var refs = new ArrayList<>(tools.values());
    refs.sort(Comparator.comparing(NPToolReference::referenceName));

    this.output.writeStartElement("Tools");
    for (final var ref : refs) {
      this.output.writeStartElement("Tool");
      this.output.writeAttribute("ReferenceName", ref.referenceName().toString());
      this.output.writeAttribute("ToolName", ref.toolName().toString());
      this.output.writeAttribute("ToolVersion", ref.version().toString());
      this.output.writeEndElement();
    }
    this.output.writeEndElement();
  }
}
