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
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.telemetry.api.NPEventSeverity;
import com.io7m.northpike.telemetry.api.NPEventType;

import java.net.URI;
import java.util.Map;

/**
 * A repository was updated.
 *
 * @param id       The ID
 * @param url      The URL
 * @param provider The provider
 * @param commits The number of new commits
 */

public record NPRepositoryUpdated(
  NPRepositoryID id,
  URI url,
  RDottedName provider,
  long commits)
  implements NPEventType
{
  @Override
  public NPEventSeverity severity()
  {
    return NPEventSeverity.INFO;
  }

  @Override
  public String name()
  {
    return "RepositoryUpdated";
  }

  @Override
  public String message()
  {
    return "Updated";
  }

  @Override
  public Map<String, String> asAttributes()
  {
    return Map.ofEntries(
      Map.entry("RepositoryID", this.id.toString()),
      Map.entry("RepositoryProvider", this.provider.value()),
      Map.entry("RepositoryURL", this.url.toString()),
      Map.entry("RepositoryCommitsNew", Long.toUnsignedString(this.commits))
    );
  }
}
