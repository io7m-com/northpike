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


package com.io7m.northpike.model;

import com.io7m.lanark.core.RDottedName;

import java.net.URI;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

/**
 * A repository.
 *
 * @param provider The SCM provider
 * @param id       The repository ID
 * @param url      The repository URL
 * @param userName The username
 * @param password The password
 */

public record NPRepository(
  RDottedName provider,
  UUID id,
  URI url,
  Optional<String> userName,
  Optional<String> password)
{
  /**
   * A repository.
   *
   * @param provider The SCM provider
   * @param id       The repository ID
   * @param url      The repository URL
   * @param userName The username
   * @param password The password
   */

  public NPRepository
  {
    Objects.requireNonNull(provider, "provider");
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(url, "url");
    Objects.requireNonNull(userName, "userName");
    Objects.requireNonNull(password, "password");
  }
}
