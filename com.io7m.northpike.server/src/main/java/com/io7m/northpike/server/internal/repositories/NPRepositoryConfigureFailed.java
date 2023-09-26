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
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.telemetry.api.NPEventSeverity;
import com.io7m.northpike.telemetry.api.NPEventType;

import java.net.URI;
import java.util.HashMap;
import java.util.Map;

/**
 * A repository could not be configured.
 *
 * @param id        The ID
 * @param url       The URL
 * @param provider  The provider
 * @param exception The exception
 */

public record NPRepositoryConfigureFailed(
  NPRepositoryID id,
  URI url,
  RDottedName provider,
  NPException exception)
  implements NPEventType
{
  @Override
  public NPEventSeverity severity()
  {
    return NPEventSeverity.ERROR;
  }

  @Override
  public String name()
  {
    return "RepositoryConfigureFailed";
  }

  @Override
  public String message()
  {
    return "ConfigureFailed";
  }

  @Override
  public Map<String, String> asAttributes()
  {
    final var attributes = new HashMap<>(this.exception.attributes());
    attributes.put("RepositoryID", this.id.toString());
    attributes.put("RepositoryProvider", this.provider.value());
    attributes.put("RepositoryURL", this.url.toString());
    return Map.copyOf(attributes);
  }
}
