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
 * Continuous integration (Tool execution language)
 */

module com.io7m.northpike.toolexec
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires com.io7m.northpike.strings;

  requires com.io7m.anethum.api;
  requires com.io7m.blackthorne.core;
  requires com.io7m.blackthorne.jxe;
  requires com.io7m.jaffirm.core;
  requires com.io7m.jdeferthrow.core;
  requires com.io7m.jlexing.core;
  requires com.io7m.jxe.core;
  requires com.io7m.lanark.core;

  exports com.io7m.northpike.toolexec.checker;
  exports com.io7m.northpike.toolexec.evaluator;
  exports com.io7m.northpike.toolexec.model;
  exports com.io7m.northpike.toolexec.parser;
  exports com.io7m.northpike.toolexec;

  exports com.io7m.northpike.toolexec.parser.v1
    to com.io7m.northpike.tests;
  exports com.io7m.northpike.toolexec.serializer.v1
    to com.io7m.northpike.tests;

}
