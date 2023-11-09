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


package com.io7m.northpike.tools.maven;

import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tools.api.NPToolFactoryType;
import com.io7m.northpike.tools.api.NPToolType;
import com.io7m.northpike.tools.maven.internal.NPTM3;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import com.io7m.verona.core.Version;
import com.io7m.verona.core.VersionRange;

import java.nio.file.Path;

/**
 * A tool factory for Maven 3.*.
 */

public final class NPTMFactory3 implements NPToolFactoryType
{
  private static final NPToolName PACKAGE_NAME =
    NPToolName.of("org.apache.maven");

  private static final VersionRange PACKAGE_VERSIONS =
    new VersionRange(
      Version.of(3, 9, 1),
      true,
      Version.of(4, 0, 0),
      false
    );

  /**
   * A tool factory for Maven 3.*.
   */

  public NPTMFactory3()
  {

  }

  @Override
  public String toString()
  {
    return "[NPTMFactory3 %s %s]"
      .formatted(this.toolName(), this.toolVersions());
  }

  @Override
  public NPToolName toolName()
  {
    return PACKAGE_NAME;
  }

  @Override
  public VersionRange toolVersions()
  {
    return PACKAGE_VERSIONS;
  }

  @Override
  public NPToolType createTool(
    final RPServiceDirectoryType services,
    final Version version,
    final Path directory)
  {
    return new NPTM3(
      services.requireService(NPStrings.class),
      version,
      directory
    );
  }

  @Override
  public String description()
  {
    return "Tool service for %s.".formatted(PACKAGE_NAME);
  }
}
