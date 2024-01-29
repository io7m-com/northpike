/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.tests.containers;

import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.northpike.tests.server.assignments.NPAssignmentFixture;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.nio.file.Files;
import java.nio.file.Path;

public final class NPFixtures
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPFixtures.class);

  private static final Path BASE_DIRECTORY;
  private static NPAssignmentFixture ASSIGNMENT_FIXTURE;
  private static NPServerFixture SERVER_FIXTURE;
  private static NPDatabaseFixture DATABASE_FIXTURE;
  private static NPIdstoreFixture IDSTORE_FIXTURE;
  private static NPPostgresFixture POSTGRES_FIXTURE;

  static {
    try {
      BASE_DIRECTORY = Files.createTempDirectory("northpike");
    } catch (final IOException e) {
      throw new IllegalStateException(e);
    }
  }

  private NPFixtures()
  {

  }

  public static int postgresPort()
  {
    return 15432;
  }

  public static int idstoreAdminPort()
  {
    return 50000;
  }

  public static int idstoreUserPort()
  {
    return 50001;
  }

  public static int idstoreUserViewPort()
  {
    return 50002;
  }

  public static String primaryIP()
  {
    final var socket = new Socket();
    try {
      socket.connect(new InetSocketAddress("www.example.com", 80));
    } catch (final IOException e) {
      // Don't care
    }
    return socket.getLocalAddress().getHostAddress();
  }

  public static NPDatabaseFixture database(
    final EContainerSupervisorType supervisor)
    throws Exception
  {
    if (DATABASE_FIXTURE == null) {
      DATABASE_FIXTURE =
        NPDatabaseFixture.create(
          supervisor,
          postgres(supervisor)
        );
    } else {
      LOG.info("Reusing northpike database fixture.");
    }
    return DATABASE_FIXTURE;
  }

  public static NPPostgresFixture postgres(
    final EContainerSupervisorType supervisor)
    throws Exception
  {
    if (POSTGRES_FIXTURE == null) {
      POSTGRES_FIXTURE =
        NPPostgresFixture.create(
          supervisor,
          primaryIP(),
          postgresPort()
        );
    } else {
      LOG.info("Reusing postgres fixture.");
    }
    return POSTGRES_FIXTURE;
  }

  public static NPIdstoreFixture idstore(
    final EContainerSupervisorType supervisor)
    throws Exception
  {
    if (IDSTORE_FIXTURE == null) {
      IDSTORE_FIXTURE =
        NPIdstoreFixture.create(
          supervisor,
          postgres(supervisor),
          BASE_DIRECTORY,
          primaryIP(),
          idstoreAdminPort(),
          idstoreUserPort(),
          idstoreUserViewPort()
        );
    } else {
      LOG.info("Reusing idstore fixture.");
    }
    return IDSTORE_FIXTURE;
  }

  public static NPServerFixture server(
    final EContainerSupervisorType supervisor)
    throws Exception
  {
    if (SERVER_FIXTURE == null) {
      SERVER_FIXTURE =
        NPServerFixture.create(
          idstore(supervisor),
          database(supervisor),
          BASE_DIRECTORY,
          primaryIP(),
          northpikeAgentAPIPort(),
          northpikeUserPort(),
          northpikeArchivePort()
        );
    } else {
      LOG.info("Reusing northpike server fixture.");
    }
    return SERVER_FIXTURE;
  }

  private static int northpikeArchivePort()
  {
    return 40002;
  }

  private static int northpikeUserPort()
  {
    return 40001;
  }

  private static int northpikeAgentAPIPort()
  {
    return 40000;
  }

  public static NPAssignmentFixture assignment(
    final EContainerSupervisorType containers)
    throws Exception
  {
    if (ASSIGNMENT_FIXTURE == null) {
      ASSIGNMENT_FIXTURE =
        NPAssignmentFixture.create(
          idstore(containers),
          database(containers),
          BASE_DIRECTORY.resolve("repositories")
        );
    }
    return ASSIGNMENT_FIXTURE;
  }
}
