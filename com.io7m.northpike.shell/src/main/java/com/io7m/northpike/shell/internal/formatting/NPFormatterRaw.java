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


package com.io7m.northpike.shell.internal.formatting;

import com.io7m.northpike.model.NPAuditEvent;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryDescription;
import org.jline.terminal.Terminal;

import java.io.PrintWriter;
import java.util.Objects;

/**
 * A raw formatter.
 */

public final class NPFormatterRaw implements NPFormatterType
{
  private final Terminal terminal;

  /**
   * A raw formatter.
   *
   * @param inTerminal The terminal
   */

  public NPFormatterRaw(
    final Terminal inTerminal)
  {
    this.terminal =
      Objects.requireNonNull(inTerminal, "terminal");
  }

  @Override
  public String toString()
  {
    return "[%s]".formatted(this.getClass().getSimpleName());
  }

  @Override
  public void formatAudits(
    final NPPage<NPAuditEvent> page)
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    out.println("# ID | Time | Owner | Type | Message");

    for (final var audit : page.items()) {
      out.printf(
        "%12s | %-24s | %-36s | %-24s | %s%n",
        Long.toUnsignedString(audit.id()),
        audit.time(),
        audit.owner(),
        audit.type(),
        audit.data()
      );
    }
    out.flush();
  }

  @Override
  public void formatRepository(
    final NPRepositoryDescription repository)
  {
    final var out = this.terminal.writer();
    out.print("ID: ");
    out.println(repository.id());
    out.print("SCM Provider: ");
    out.println(repository.provider());
    out.print("URI: ");
    out.println(repository.url());
    out.print("Credentials: ");
    out.println(repository.credentials());
    out.print("Signing Policy: ");
    out.println(repository.signingPolicy());
    out.flush();
  }

  private static void formatPage(
    final NPPage<?> page,
    final PrintWriter out)
  {
    out.printf(
      "# Page %s of %s, offset %s%n",
      Integer.toUnsignedString(page.pageIndex()),
      Integer.toUnsignedString(page.pageCount()),
      Long.toUnsignedString(page.pageFirstOffset())
    );
  }
}
