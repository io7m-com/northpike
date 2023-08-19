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


package com.io7m.northpike.server.configuration.v1;

import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.northpike.server.api.NPServerDirectoryConfiguration;
import org.xml.sax.Attributes;

import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * A parser for {@link NPServerDirectoryConfiguration}
 */

public final class NPSC1Directories
  implements BTElementHandlerType<Object, NPServerDirectoryConfiguration>
{
  private Path reposDirectory;
  private Path archiveDirectory;

  /**
   * A parser for {@link NPServerDirectoryConfiguration}
   *
   * @param context The parse context
   */

  public NPSC1Directories(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.reposDirectory =
      Paths.get(attributes.getValue("RepositoryDirectory"));
    this.archiveDirectory =
      Paths.get(attributes.getValue("ArchiveDirectory"));
  }

  @Override
  public NPServerDirectoryConfiguration onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPServerDirectoryConfiguration(
      this.reposDirectory,
      this.archiveDirectory
    );
  }
}
