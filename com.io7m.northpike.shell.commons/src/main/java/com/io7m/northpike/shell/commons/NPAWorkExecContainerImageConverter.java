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


package com.io7m.northpike.shell.commons;

import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorContainerImage;
import com.io7m.quarrel.core.QValueConverterType;

import java.util.Optional;

/**
 * @see NPAWorkExecutorContainerImage
 */

public final class NPAWorkExecContainerImageConverter
  implements QValueConverterType<NPAWorkExecutorContainerImage>
{
  /**
   * @see NPAWorkExecutorContainerImage
   */

  public NPAWorkExecContainerImageConverter()
  {

  }

  @Override
  public NPAWorkExecutorContainerImage convertFromString(
    final String text)
  {
    return NPAWorkExecutorContainerImage.of(text);
  }

  @Override
  public String convertToString(
    final NPAWorkExecutorContainerImage value)
  {
    return value.toString();
  }

  @Override
  public NPAWorkExecutorContainerImage exampleValue()
  {
    return new NPAWorkExecutorContainerImage(
      "quay.io",
      "io7mcom/idstore",
      "1.0.0",
      Optional.of("sha256:75796f97f4b5b51e7f6bec3673ba442b85cb6486bf737a37ce51d90266b4e176")
    );
  }

  @Override
  public String syntax()
  {
    return "<repository> '/' <name> ':' <tag> '@' <hash>";
  }

  @Override
  public Class<NPAWorkExecutorContainerImage> convertedClass()
  {
    return NPAWorkExecutorContainerImage.class;
  }
}
