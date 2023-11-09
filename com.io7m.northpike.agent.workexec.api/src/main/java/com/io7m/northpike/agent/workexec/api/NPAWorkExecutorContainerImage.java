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


package com.io7m.northpike.agent.workexec.api;

import java.util.Objects;
import java.util.Optional;

/**
 * A reference to a container image.
 *
 * @param registry The container registry (such as "quay.io")
 * @param name     The image name (such as "io7mcom/idstore")
 * @param tag      The image tag (such as "1.0.0-beta0013")
 * @param hash     The image hash (such as "sha256:ab38fabce3")
 */

public record NPAWorkExecutorContainerImage(
  String registry,
  String name,
  String tag,
  Optional<String> hash)
{
  /**
   * A reference to a container image.
   *
   * @param registry The container registry (such as "quay.io")
   * @param name     The image name (such as "io7mcom/idstore")
   * @param tag      The image tag (such as "1.0.0-beta0013")
   * @param hash     The image hash (such as "sha256:ab38fabce3")
   */

  public NPAWorkExecutorContainerImage
  {
    Objects.requireNonNull(registry, "registry");
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(tag, "tag");
    Objects.requireNonNull(hash, "hash");
  }
}
