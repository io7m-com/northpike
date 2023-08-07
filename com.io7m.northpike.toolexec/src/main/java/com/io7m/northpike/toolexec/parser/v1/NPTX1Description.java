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


package com.io7m.northpike.toolexec.parser.v1;

import com.io7m.blackthorne.api.BTElementHandlerConstructorType;
import com.io7m.blackthorne.api.BTElementHandlerType;
import com.io7m.blackthorne.api.BTElementParsingContextType;
import com.io7m.blackthorne.api.BTQualifiedName;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.toolexec.NPTXDescription;
import com.io7m.northpike.toolexec.NPTXStatementType;
import org.xml.sax.Attributes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * A {@code ToolExecution} element handler.
 */

public final class NPTX1Description
  implements BTElementHandlerType<NPTXStatementType, NPTXDescription>
{
  private final ArrayList<NPTXStatementType> statements;
  private RDottedName name;
  private long version;

  /**
   * A {@code ToolExecution} element handler.
   *
   * @param context The parse context
   */

  public NPTX1Description(
    final BTElementParsingContextType context)
  {
    this.statements = new ArrayList<>();
  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPTXStatementType>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return NPTX1Statements.statements();
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final NPTXStatementType result)
  {
    this.statements.add(result);
  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.name =
      new RDottedName(attributes.getValue("Name"));
    this.version =
      Long.parseUnsignedLong(attributes.getValue("Version"));
  }

  @Override
  public NPTXDescription onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPTXDescription(
      this.name,
      this.version,
      List.copyOf(this.statements)
    );
  }
}
