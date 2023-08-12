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


package com.io7m.northpike.agent.expressions.v1;

import com.io7m.northpike.agent.expressions.NAESchemas;
import com.io7m.northpike.model.NPAgentLabelMatchType;
import com.io7m.northpike.model.NPAgentLabelMatchType.And;
import com.io7m.northpike.model.NPAgentLabelMatchType.AnyLabel;
import com.io7m.northpike.model.NPAgentLabelMatchType.Or;
import com.io7m.northpike.model.NPAgentLabelMatchType.Specific;

import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;
import java.io.OutputStream;

/**
 * A serializer for agent label expressions (v1) data.
 */

public final class NAE1Serializer
{
  private final XMLOutputFactory outputs;
  private final XMLStreamWriter output;
  private final String ns;

  private NAE1Serializer(
    final OutputStream outputStream)
    throws XMLStreamException
  {
    this.outputs =
      XMLOutputFactory.newFactory();
    this.output =
      this.outputs.createXMLStreamWriter(outputStream, "UTF-8");
    this.ns =
      NAESchemas.labelExpressions1().namespace().toString();
  }

  /**
   * A serializer for agent label expressions (v1) data.
   *
   * @param outputStream The output stream
   *
   * @return A serializer
   *
   * @throws XMLStreamException On errors
   */

  public static NAE1Serializer create(
    final OutputStream outputStream)
    throws XMLStreamException
  {
    return new NAE1Serializer(outputStream);
  }

  /**
   * Execute the serializer.
   *
   * @param expression The input expression
   *
   * @throws XMLStreamException On errors
   */

  public void serialize(
    final NPAgentLabelMatchType expression)
    throws XMLStreamException
  {
    this.output.writeStartDocument("UTF-8", "1.0");
    this.serializeExpression(true, expression);
    this.output.writeEndDocument();
  }

  private void serializeExpression(
    final boolean first,
    final NPAgentLabelMatchType expression)
    throws XMLStreamException
  {
    if (expression instanceof final AnyLabel anyLabel) {
      this.serializeExpressionAnyLabel(first, anyLabel);
      return;
    }
    if (expression instanceof final And and) {
      this.serializeExpressionAnd(first, and);
      return;
    }
    if (expression instanceof final Or or) {
      this.serializeExpressionOr(first, or);
      return;
    }
    if (expression instanceof final Specific specific) {
      this.serializeExpressionSpecific(first, specific);
      return;
    }
  }

  private void serializeExpressionSpecific(
    final boolean first,
    final Specific specific)
    throws XMLStreamException
  {
    if (first) {
      this.output.writeStartElement("WithLabel");
      this.output.writeDefaultNamespace(this.ns);
    } else {
      this.output.writeStartElement(this.ns, "WithLabel");
    }
    this.output.writeAttribute("Name", specific.name().value());
    this.output.writeEndElement();
  }

  private void serializeExpressionOr(
    final boolean first,
    final Or or)
    throws XMLStreamException
  {
    if (first) {
      this.output.writeStartElement("Or");
      this.output.writeDefaultNamespace(this.ns);
    } else {
      this.output.writeStartElement(this.ns, "Or");
    }
    this.serializeExpression(false, or.e0());
    this.serializeExpression(false, or.e1());
    this.output.writeEndElement();
  }

  private void serializeExpressionAnd(
    final boolean first,
    final And and)
    throws XMLStreamException
  {
    if (first) {
      this.output.writeStartElement("And");
      this.output.writeDefaultNamespace(this.ns);
    } else {
      this.output.writeStartElement(this.ns, "And");
    }
    this.serializeExpression(false, and.e0());
    this.serializeExpression(false, and.e1());
    this.output.writeEndElement();
  }

  private void serializeExpressionAnyLabel(
    final boolean first,
    final AnyLabel anyLabel)
    throws XMLStreamException
  {
    if (first) {
      this.output.writeStartElement("AnyLabel");
      this.output.writeDefaultNamespace(this.ns);
      this.output.writeEndElement();
    } else {
      this.output.writeEmptyElement(this.ns, "AnyLabel");
    }
  }
}
