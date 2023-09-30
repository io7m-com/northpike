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
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositorySummary;
import com.io7m.tabla.core.TTableRendererType;
import com.io7m.tabla.core.TTableType;
import com.io7m.tabla.core.TTableWidthConstraintRange;
import com.io7m.tabla.core.Tabla;
import org.apache.commons.lang3.StringUtils;
import org.jline.terminal.Terminal;

import java.io.PrintWriter;
import java.time.OffsetDateTime;
import java.util.Objects;

import static com.io7m.tabla.core.TColumnWidthConstraint.atLeastContentOrHeader;
import static com.io7m.tabla.core.TConstraintHardness.SOFT_CONSTRAINT;
import static com.io7m.tabla.core.TTableWidthConstraintType.tableWidthExact;

/**
 * A pretty formatter.
 */

public final class NPFormatterPretty implements NPFormatterType
{
  private final Terminal terminal;
  private final TTableRendererType tableRenderer;

  /**
   * A pretty formatter.
   *
   * @param inTerminal The terminal
   */

  public NPFormatterPretty(
    final Terminal inTerminal)
  {
    this.terminal =
      Objects.requireNonNull(inTerminal, "terminal");
    this.tableRenderer =
      Tabla.framedUnicodeRenderer();
  }

  @Override
  public String toString()
  {
    return "[%s]".formatted(this.getClass().getSimpleName());
  }

  private int width()
  {
    var width = Math.max(0, this.terminal.getWidth());
    if (width == 0) {
      width = 80;
    }
    return width;
  }

  private int widthFor(
    final int columns)
  {
    final var columnPad = 2;
    final var columnEdge = 1;
    return this.width() - (2 + (columns * (columnEdge + columnPad)));
  }

  private TTableWidthConstraintRange softTableWidth(
    final int columns)
  {
    return tableWidthExact(this.widthFor(columns), SOFT_CONSTRAINT);
  }

  @Override
  public void formatAudits(
    final NPPage<NPAuditEvent> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(5))
        .declareColumn("ID", atLeastContentOrHeader())
        .declareColumn("Time", atLeastContentOrHeader())
        .declareColumn("Owner", atLeastContentOrHeader())
        .declareColumn("Type", atLeastContentOrHeader())
        .declareColumn("Data", atLeastContentOrHeader());

    for (final var audit : page.items()) {
      builder.addRow()
        .addCell(Long.toUnsignedString(audit.id()))
        .addCell(audit.time().toString())
        .addCell(audit.owner().toString())
        .addCell(audit.type())
        .addCell(audit.data().toString());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatRepository(
    final NPRepositoryDescription repository)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Attribute", atLeastContentOrHeader())
        .declareColumn("Value", atLeastContentOrHeader());

    builder.addRow()
      .addCell("Repository ID")
      .addCell(repository.id().toString());
    builder.addRow()
      .addCell("SCM Provider")
      .addCell(repository.provider().toString());
    builder.addRow()
      .addCell("URI")
      .addCell(repository.url().toString());
    builder.addRow()
      .addCell("Credentials")
      .addCell(repository.credentials().toString());
    builder.addRow()
      .addCell("Signing Policy")
      .addCell(repository.signingPolicy().toString());

    this.renderTable(builder.build());
  }

  @Override
  public void formatRepositorySummaries(
    final NPPage<NPRepositorySummary> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(3))
        .declareColumn("ID", atLeastContentOrHeader())
        .declareColumn("Provider", atLeastContentOrHeader())
        .declareColumn("URI", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.id().toString())
        .addCell(item.provider().value())
        .addCell(item.url().toString());
    }

    this.renderTable(builder.build());
  }

  @Override
  public void formatPublicKey(
    final NPPublicKey key)
    throws Exception
  {
    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(2))
        .declareColumn("Attribute", atLeastContentOrHeader())
        .declareColumn("Value", atLeastContentOrHeader());

    builder.addRow()
      .addCell("Fingerprint")
      .addCell(key.fingerprint().value());
    builder.addRow()
      .addCell("Time Created")
      .addCell(key.timeCreated().toString());
    builder.addRow()
      .addCell("Time Expires")
      .addCell(
        key.timeExpires()
          .map(OffsetDateTime::toString)
          .orElse("Never")
      );

    for (final var user : key.userIDs()) {
      builder.addRow()
        .addCell("User ID")
        .addCell(user);
    }

    this.renderTable(builder.build());

    final var out = this.terminal.writer();
    out.println(key.encodedForm());
    out.flush();
  }

  @Override
  public void formatPublicKeySummaries(
    final NPPage<NPPublicKey> page)
    throws Exception
  {
    final var out = this.terminal.writer();
    formatPage(page, out);

    final var builder =
      Tabla.builder()
        .setWidthConstraint(this.softTableWidth(4))
        .declareColumn("Fingerprint", atLeastContentOrHeader())
        .declareColumn("Time Created", atLeastContentOrHeader())
        .declareColumn("Time Expires", atLeastContentOrHeader())
        .declareColumn("User IDs", atLeastContentOrHeader());

    for (final var item : page.items()) {
      builder.addRow()
        .addCell(item.fingerprint().toString())
        .addCell(item.timeCreated().withNano(0).toString())
        .addCell(
          item.timeExpires()
            .map(x -> x.withNano(0))
            .map(OffsetDateTime::toString)
            .orElse("Never")
        )
        .addCell(
          StringUtils.abbreviate(
            String.join(", ", item.userIDs()), 30
          )
        );
    }

    this.renderTable(builder.build());
  }

  private static void formatPage(
    final NPPage<?> page,
    final PrintWriter out)
  {
    out.printf(
      " Page %s of %s, offset %s%n",
      Integer.toUnsignedString(page.pageIndex()),
      Integer.toUnsignedString(page.pageCount()),
      Long.toUnsignedString(page.pageFirstOffset())
    );
  }

  private void renderTable(
    final TTableType table)
  {
    final var lines =
      this.tableRenderer.renderLines(table);

    final var writer = this.terminal.writer();
    for (final var line : lines) {
      writer.println(line);
    }
  }
}
