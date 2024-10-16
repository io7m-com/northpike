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


package com.io7m.northpike.server.internal.repositories;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPDocumentation;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.telemetry.api.NPEventSeverity;

import java.net.URI;
import java.nio.file.Path;
import java.util.Map;

/**
 * An archive was created by the repository.
 *
 * @param id       The ID
 * @param url      The URL
 * @param provider The provider
 * @param file     The created file
 * @param size     The file size
 */

@NPDocumentation("An archive was created by the repository service.")
public record NPRepositoryArchiveCreated(
  NPRepositoryID id,
  URI url,
  RDottedName provider,
  Path file,
  long size)
  implements NPRepositoryEventType
{
  @Override
  public NPEventSeverity severity()
  {
    return NPEventSeverity.INFO;
  }

  @Override
  public String name()
  {
    return "RepositoryArchiveCreated";
  }

  @Override
  public String message()
  {
    return "RepositoryArchiveCreated";
  }

  @Override
  public Map<String, String> asAttributes()
  {
    return Map.ofEntries(
      Map.entry("RepositoryID", this.id.toString()),
      Map.entry("RepositoryProvider", this.provider.value()),
      Map.entry("RepositoryURL", this.url.toString()),
      Map.entry("RepositoryArchiveFile", this.file.toString()),
      Map.entry("RepositoryArchiveFileSize", Long.toUnsignedString(this.size))
    );
  }
}
