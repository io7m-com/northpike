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


package com.io7m.northpike.server.internal.archives;

import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesArchivesType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.server.api.NPServerDirectoryConfiguration;
import org.eclipse.jetty.http.HttpFields;
import org.eclipse.jetty.io.Content;
import org.eclipse.jetty.io.content.PathContentSource;
import org.eclipse.jetty.server.Handler;
import org.eclipse.jetty.server.Request;
import org.eclipse.jetty.server.Response;
import org.eclipse.jetty.util.Callback;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Objects;
import java.util.Optional;
import java.util.regex.Pattern;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE_READ_ONLY;

/**
 * A handler that serves archives by ID.
 */

public final class NPArchiveHandler extends Handler.Abstract
{
  private static final Pattern LEADING_SLASHES =
    Pattern.compile("^/+");

  private final NPDatabaseType database;
  private final NPServerDirectoryConfiguration directories;

  /**
   * A handler that serves archives by ID.
   *
   * @param inDatabase    The database
   * @param inDirectories The directories
   */

  public NPArchiveHandler(
    final NPDatabaseType inDatabase,
    final NPServerDirectoryConfiguration inDirectories)
  {
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.directories =
      Objects.requireNonNull(inDirectories, "directories");
  }

  @Override
  public boolean handle(
    final Request request,
    final Response response,
    final Callback callback)
  {
    final var headers = response.getHeaders();

    try {
      final var archiveOpt = this.findArchive(request);
      if (archiveOpt.isEmpty()) {
        response.setStatus(404);
        headers.put("Content-Type", "text/plain");
        response.write(true, messageBytes("Not found."), callback);
        return true;
      }

      final var archive = archiveOpt.get();
      this.copyFileOut(response, callback, headers, archive);
      return true;
    } catch (final Exception e) {
      response.setStatus(500);
      headers.put("Content-Type", "text/plain");
      response.write(true, messageBytes(e.getMessage()), callback);
      return true;
    } finally {
      callback.succeeded();
    }
  }

  private void copyFileOut(
    final Response response,
    final Callback callback,
    final HttpFields.Mutable headers,
    final NPArchive archive)
    throws IOException
  {
    headers.put("Content-Type", "application/octet-stream");

    final var file =
      this.directories.archiveDirectory()
        .resolve(archive.token().value() + ".tgz");

    final var size = Files.size(file);
    headers.put("Content-Length", Long.toUnsignedString(size));
    Content.copy(new PathContentSource(file), response, callback);
  }

  private static ByteBuffer messageBytes(
    final String message)
  {
    return ByteBuffer.wrap(message.getBytes(StandardCharsets.UTF_8));
  }

  private Optional<NPArchive> findArchive(
    final Request request)
    throws NPDatabaseException
  {
    final var uri =
      request.getHttpURI();
    final var path =
      uri.getPath();
    final var withoutLeading =
      LEADING_SLASHES.matcher(path).replaceFirst("");
    final var token =
      new NPToken(withoutLeading);

    try (var connection =
           this.database.openConnection(NORTHPIKE_READ_ONLY)) {
      try (var transaction =
             connection.openTransaction()) {
        final var get =
          transaction.queries(NPDatabaseQueriesArchivesType.GetType.class);
        return get.execute(token);
      }
    }
  }
}
