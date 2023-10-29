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


package com.io7m.northpike.agent.configuration.v1;

import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorContainerImage;
import org.xml.sax.Attributes;

import java.util.Optional;

/**
 * Element parser.
 */

public final class NPAC1Image
  implements BTElementHandlerType<Object, NPAWorkExecutorContainerImage>
{
  private NPAWorkExecutorContainerImage image;

  /**
   * Element parser.
   *
   * @param context The parse context
   */

  public NPAC1Image(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.image =
      new NPAWorkExecutorContainerImage(
        attributes.getValue("Registry"),
        attributes.getValue("Name"),
        attributes.getValue("Tag"),
        Optional.ofNullable(attributes.getValue("Hash"))
      );
  }

  @Override
  public NPAWorkExecutorContainerImage onElementFinished(
    final BTElementParsingContextType context)
  {
    return this.image;
  }
}
