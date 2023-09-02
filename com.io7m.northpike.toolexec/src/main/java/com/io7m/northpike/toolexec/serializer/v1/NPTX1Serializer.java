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

import com.io7m.anethum.api.SerializationException;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.toolexec.NPTXFormats;
import com.io7m.northpike.toolexec.NPTXSchemas;
import com.io7m.northpike.toolexec.NPTXSerializerType;
import com.io7m.northpike.toolexec.model.NPTXComment;
import com.io7m.northpike.toolexec.model.NPTXDescription;
import com.io7m.northpike.toolexec.model.NPTXEAnd;
import com.io7m.northpike.toolexec.model.NPTXEFalse;
import com.io7m.northpike.toolexec.model.NPTXEIsEqual;
import com.io7m.northpike.toolexec.model.NPTXENot;
import com.io7m.northpike.toolexec.model.NPTXENumber;
import com.io7m.northpike.toolexec.model.NPTXEOr;
import com.io7m.northpike.toolexec.model.NPTXEString;
import com.io7m.northpike.toolexec.model.NPTXEStringSetContains;
import com.io7m.northpike.toolexec.model.NPTXETrue;
import com.io7m.northpike.toolexec.model.NPTXEVariableBoolean;
import com.io7m.northpike.toolexec.model.NPTXEVariableNumber;
import com.io7m.northpike.toolexec.model.NPTXEVariableString;
import com.io7m.northpike.toolexec.model.NPTXEVariableStringSet;
import com.io7m.northpike.toolexec.model.NPTXExpressionType;
import com.io7m.northpike.toolexec.model.NPTXSArgumentAdd;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentClear;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentPass;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentRemove;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentSet;
import com.io7m.northpike.toolexec.model.NPTXSIf;
import com.io7m.northpike.toolexec.model.NPTXStatementType;

import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.util.List;

/**
 * A serializer for toolexec v1 data.
 */

public final class NPTX1Serializer implements NPTXSerializerType
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

  /**
   * Create a serializer for toolexec v1 data.
   *
   * @param outputStream The output stream
   *
   * @return A serializer
   */

  public static NPTX1Serializer create(
    final OutputStream outputStream)
  {
    try {
      return new NPTX1Serializer(outputStream);
    } catch (final XMLStreamException e) {
      throw new IllegalStateException(e);
    }
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
    if (statement instanceof final NPTXComment s) {
      this.serializeComment(s);
      return;
    }

    throw new IllegalStateException();
  }

  private void serializeComment(
    final NPTXComment statement)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "Comment");
    this.output.writeCharacters(statement.text());
    this.output.writeEndElement();
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
    if (expression instanceof final NPTXEVariableStringSet e) {
      this.serializeExpressionVariableStringSet(e);
      return;
    }
    if (expression instanceof final NPTXEAnd e) {
      this.serializeExpressionAnd(e);
      return;
    }
    if (expression instanceof final NPTXEOr e) {
      this.serializeExpressionOr(e);
      return;
    }
    if (expression instanceof final NPTXENot e) {
      this.serializeExpressionNot(e);
      return;
    }
    if (expression instanceof final NPTXEStringSetContains e) {
      this.serializeExpressionStringSetContains(e);
      return;
    }

    throw new IllegalStateException();
  }

  private void serializeExpressionStringSetContains(
    final NPTXEStringSetContains e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "StringSetContains");
    this.output.writeAttribute("Value", e.value());
    this.serializeExpression(e.e0());
    this.output.writeEndElement();
  }

  private void serializeExpressionNot(
    final NPTXENot e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "Not");
    this.serializeExpression(e.e0());
    this.output.writeEndElement();
  }

  private void serializeExpressionOr(
    final NPTXEOr e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "Or");
    this.serializeExpression(e.e0());
    this.serializeExpression(e.e1());
    this.output.writeEndElement();
  }

  private void serializeExpressionAnd(
    final NPTXEAnd e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "And");
    this.serializeExpression(e.e0());
    this.serializeExpression(e.e1());
    this.output.writeEndElement();
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

  private void serializeExpressionVariableStringSet(
    final NPTXEVariableStringSet e)
    throws XMLStreamException
  {
    this.output.writeStartElement(this.ns, "VariableStringSet");
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

  @Override
  public NPFormatName format()
  {
    return NPTXFormats.nptx1();
  }

  @Override
  public void execute(
    final NPTXDescription description)
    throws SerializationException
  {
    try {
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
    } catch (final XMLStreamException e) {
      throw new SerializationException(e.getMessage(), e);
    }
  }

  @Override
  public void close()
    throws IOException
  {
    try {
      this.output.close();
    } catch (final XMLStreamException e) {
      throw new IOException(e);
    }
  }
}
