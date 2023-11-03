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

/**
 * Continuous integration (Shell)
 */

module com.io7m.northpike.shell
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires com.io7m.northpike.keys;
  requires com.io7m.northpike.model;
  requires com.io7m.northpike.protocol.user;
  requires com.io7m.northpike.strings;
  requires com.io7m.northpike.toolexec;
  requires com.io7m.northpike.user_client.api;

  requires com.io7m.anethum.api;
  requires com.io7m.jmulticlose.core;
  requires com.io7m.quarrel.core;
  requires com.io7m.repetoir.core;
  requires com.io7m.tabla.core;
  requires org.apache.commons.lang3;
  requires org.jline;

  exports com.io7m.northpike.shell;
}
