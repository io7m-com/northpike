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

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorContainerImage;
import org.xml.sax.Attributes;

import java.nio.file.Paths;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * Element parser.
 */

public final class NPAC1WorkExecutorConfiguration
  implements BTElementHandlerType<
  NPAWorkExecutorContainerImage, NPAWorkExecutorConfiguration>
{
  private final NPAWorkExecutorConfiguration.Builder builder;
  private NPAWorkExecutorContainerImage image;

  /**
   * Element parser.
   *
   * @param context The parse context
   */

  public NPAC1WorkExecutorConfiguration(
    final BTElementParsingContextType context)
  {
    this.builder = NPAWorkExecutorConfiguration.builder();
  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPAWorkExecutorContainerImage>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      Map.entry(
        NPACv1.element("OCIImage"),
        NPAC1Image::new
      )
    );
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final NPAWorkExecutorContainerImage result)
  {
    this.image = Objects.requireNonNull(result, "result");
  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.builder.setExecutorType(
      new RDottedName(attributes.getValue("Type"))
    );
    this.builder.setTemporaryDirectory(
      Paths.get(attributes.getValue("TemporaryDirectory"))
    );
    this.builder.setWorkDirectory(
      Paths.get(attributes.getValue("WorkDirectory"))
    );

    Optional.ofNullable(
      attributes.getValue("WorkExecDistributionDirectory")
    ).ifPresent(p -> {
      this.builder.setWorkExecDistributionDirectory(Paths.get(p));
    });
  }

  @Override
  public NPAWorkExecutorConfiguration onElementFinished(
    final BTElementParsingContextType context)
  {
    if (this.image != null) {
      this.builder.setContainerImage(this.image);
    }
    return this.builder.build();
  }
}
