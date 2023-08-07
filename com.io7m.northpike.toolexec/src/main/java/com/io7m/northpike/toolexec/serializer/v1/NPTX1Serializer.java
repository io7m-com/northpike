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


package com.io7m.northpike.toolexec.serializer.v1;

import com.io7m.northpike.toolexec.NPTXDescription;
import com.io7m.northpike.toolexec.NPTXEFalse;
import com.io7m.northpike.toolexec.NPTXEIsEqual;
import com.io7m.northpike.toolexec.NPTXENumber;
import com.io7m.northpike.toolexec.NPTXEString;
import com.io7m.northpike.toolexec.NPTXETrue;
import com.io7m.northpike.toolexec.NPTXEVariableBoolean;
import com.io7m.northpike.toolexec.NPTXEVariableNumber;
import com.io7m.northpike.toolexec.NPTXEVariableString;
import com.io7m.northpike.toolexec.NPTXExpressionType;
import com.io7m.northpike.toolexec.NPTXSArgumentAdd;
import com.io7m.northpike.toolexec.NPTXSEnvironmentClear;
import com.io7m.northpike.toolexec.NPTXSEnvironmentPass;
import com.io7m.northpike.toolexec.NPTXSEnvironmentRemove;
import com.io7m.northpike.toolexec.NPTXSEnvironmentSet;
import com.io7m.northpike.toolexec.NPTXSIf;
import com.io7m.northpike.toolexec.NPTXSchemas;
import com.io7m.northpike.toolexec.NPTXStatementType;

import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;
import java.io.OutputStream;
import java.util.List;

public final class NPTX1Serializer
{
  private final XMLOutputFactory outputs;
  private final XMLStreamWriter output;
  private final String ns;

  private NPTX1Serializer(
    final OutputStream outputStream)
    throws XMLStreamException
  {
    this.outputs =
      XMLOutputFactory.newFactory();
    this.output =
      this.outputs.createXMLStreamWriter(outputStream, "UTF-8");
    this.ns =
      NPTXSchemas.schema1().namespace().toString();
  }

  public static NPTX1Serializer create(
    final OutputStream outputStream)
    throws XMLStreamException
  {
    return new NPTX1Serializer(outputStream);
  }

  public void serialize(
    final NPTXDescription description)
    throws XMLStreamException
  {
    this.output.writeStartDocument("UTF-8", "1.0");
    this.output.writeStartElement("ToolExecution");
    this.output.writeDefaultNamespace(this.ns);

    this.output.writeAttribute(
      "Name",
      description.name().value()
    );
    this.output.writeAttribute(
      "Version",
      Long.toUnsignedString(description.version())
    );

    for (final var statement : description.statements()) {
      this.serializeStatement(statement);
    }

    this.output.writeEndElement();
    this.output.writeEndDocument();
  }

  private void serializeStatement(
    final NPTXStatementType statement)
    throws XMLStreamException
  {
    if (statement instanceof final NPTXSEnvironmentClear s) {
      this.serializeStatementEnvironmentClear(s);
      return;
    }
    if (statement instanceof final NPTXSEnvironmentPass s) {
      this.serializeStatementEnvironmentPass(s);
      return;
    }
    if (statement instanceof final NPTXSEnvironmentRemove s) {
      this.serializeStatementEnvironmentRemove(s);
      return;
    }
    if (statement instanceof final NPTXSEnvironmentSet s) {
      this.serializeStatementEnvironmentSet(s);
      return;
    }
    if (statement instanceof final NPTXSArgumentAdd s) {
      this.serializeStatementArgumentAdd(s);
      return;
    }
    if (statement instanceof final NPTXSIf s) {
      this.serializeStatementIf(s);
      return;
    }
  }

  private void serializeStatementIf(
    final NPTXSIf statement)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "If");
    this.serializeCondition(statement.condition());
    this.serializeThen(statement.branchTrue());
    this.serializeElse(statement.branchFalse());
    this.output.writeEndElement();
  }

  private void serializeCondition(
    final NPTXExpressionType condition)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "Condition");
    this.serializeExpression(condition);
    this.output.writeEndElement();
  }

  private void serializeElse(
    final List<NPTXStatementType> statements)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "Else");
    for (final var statement : statements) {
      this.serializeStatement(statement);
    }
    this.output.writeEndElement();
  }

  private void serializeThen(
    final List<NPTXStatementType> statements)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "Then");
    for (final var statement : statements) {
      this.serializeStatement(statement);
    }
    this.output.writeEndElement();
  }

  private void serializeStatementArgumentAdd(
    final NPTXSArgumentAdd statement)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "ArgumentAdd");
    this.output.writeAttribute("Value", statement.value());
    this.output.writeEndElement();
  }

  private void serializeStatementEnvironmentSet(
    final NPTXSEnvironmentSet statement)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "EnvironmentSet");
    this.output.writeAttribute("Name", statement.name());
    this.output.writeAttribute("Value", statement.value());
    this.output.writeEndElement();
  }

  private void serializeStatementEnvironmentRemove(
    final NPTXSEnvironmentRemove statement)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "EnvironmentRemove");
    this.output.writeAttribute("Name", statement.name());
    this.output.writeEndElement();
  }

  private void serializeStatementEnvironmentPass(
    final NPTXSEnvironmentPass statement)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "EnvironmentPass");
    this.output.writeAttribute("Name", statement.name());
    this.output.writeEndElement();
  }

  private void serializeStatementEnvironmentClear(
    final NPTXSEnvironmentClear statement)
    throws XMLStreamException
  {
    this.output.writeEmptyElement(this.ns, "EnvironmentClear");
  }

  private void serializeExpression(
    final NPTXExpressionType expression)
    throws XMLStreamException
  {
    if (expression instanceof final NPTXETrue e) {
      this.serializeExpressionTrue(e);
      return;
    }
    if (expression instanceof final NPTXEFalse e) {
      this.serializeExpressionFalse(e);
      return;
    }
    if (expression instanceof final NPTXENumber e) {
      this.serializeExpressionNumber(e);
      return;
    }
    if (expression instanceof final NPTXEString e) {
      this.serializeExpressionString(e);
      return;
    }
    if (expression instanceof final NPTXEIsEqual e) {
      this.serializeExpressionIsEqual(e);
      return;
    }
    if (expression instanceof final NPTXEVariableBoolean e) {
      this.serializeExpressionVariableBoolean(e);
      return;
    }
    if (expression instanceof final NPTXEVariableNumber e) {
      this.serializeExpressionVariableNumber(e);
      return;
    }
    if (expression instanceof final NPTXEVariableString e) {
      this.serializeExpressionVariableString(e);
      return;
    }
  }

  private void serializeExpressionIsEqual(
    final NPTXEIsEqual e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "IsEqual");
    this.serializeExpression(e.e0());
    this.serializeExpression(e.e1());
    this.output.writeEndElement();
  }

  private void serializeExpressionNumber(
    final NPTXENumber e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "Number");
    this.output.writeAttribute("Value", e.value().toString());
    this.output.writeEndElement();
  }

  private void serializeExpressionString(
    final NPTXEString e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "String");
    this.output.writeAttribute("Value", e.value());
    this.output.writeEndElement();
  }

  private void serializeExpressionVariableBoolean(
    final NPTXEVariableBoolean e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "VariableBoolean");
    this.output.writeAttribute("Name", e.name().value());
    this.output.writeEndElement();
  }

  private void serializeExpressionVariableNumber(
    final NPTXEVariableNumber e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "VariableNumber");
    this.output.writeAttribute("Name", e.name().value());
    this.output.writeEndElement();
  }

  private void serializeExpressionVariableString(
    final NPTXEVariableString e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "VariableString");
    this.output.writeAttribute("Name", e.name().value());
    this.output.writeEndElement();
  }

  private void serializeExpressionFalse(
    final NPTXEFalse e)
    throws XMLStreamException
  {
    this.output.writeEmptyElement(this.ns, "False");
  }

  private void serializeExpressionTrue(
    final NPTXETrue e)
    throws XMLStreamException
  {
    this.output.writeEmptyElement(this.ns, "True");
  }
}
