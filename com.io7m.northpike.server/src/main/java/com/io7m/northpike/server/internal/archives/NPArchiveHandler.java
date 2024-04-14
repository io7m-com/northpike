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
import io.helidon.webserver.http.Handler;
import io.helidon.webserver.http.ServerRequest;
import io.helidon.webserver.http.ServerResponse;

import java.io.IOException;
import java.nio.file.Files;
import java.util.Objects;
import java.util.Optional;
import java.util.regex.Pattern;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE_READ_ONLY;
import static io.helidon.http.HeaderNames.CONTENT_TYPE;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A static file handler.
 */

public final class NPArchiveHandler implements Handler
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
  public void handle(
    final ServerRequest request,
    final ServerResponse response)
    throws Exception
  {
    final var archiveOpt = this.findArchive(request);
    if (archiveOpt.isEmpty()) {
      response.status(404);
      response.header(CONTENT_TYPE, "text/plain");
      response.send("Not found.\r\n".getBytes(UTF_8));
      return;
    }

    this.copyFileOut(response, archiveOpt.get());
  }

  private void copyFileOut(
    final ServerResponse response,
    final NPArchive archive)
    throws IOException
  {
    response.header(CONTENT_TYPE, "application/octet-stream");

    final var file =
      this.directories.archiveDirectory()
        .resolve(archive.token().value() + ".tgz");

    final var size = Files.size(file);
    response.contentLength(size);

    try (var input = Files.newInputStream(file)) {
      final var output = response.outputStream();
      input.transferTo(output);
      output.flush();
    }
  }

  private Optional<NPArchive> findArchive(
    final ServerRequest request)
    throws NPDatabaseException
  {
    final var path =
      request.path()
        .absolute()
        .path();
    final var withoutLeading =
      LEADING_SLASHES.matcher(path).replaceFirst("");
    final var token =
      new NPToken(withoutLeading);

    try (var connection =
           this.database.openConnection(NORTHPIKE_READ_ONLY)) {
      try (var transaction =
             connection.openTransaction()) {
        final var get =
          transaction.queries(NPDatabaseQueriesArchivesType.ArchiveGetType.class);
        return get.execute(token);
      }
    }
  }
}
