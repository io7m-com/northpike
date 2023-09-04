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


package com.io7m.northpike.tests.containers;

import com.io7m.ervilla.api.EContainerSupervisorType;

import java.nio.file.Files;

public final class NPTestContainerInstances
{
  private static NPTestContainers.NPIdstoreFixture IDSTORE_FIXTURE;
  private static NPTestContainers.NPDatabaseFixture DATABASE_FIXTURE;
  private static NPTestContainers.NPServerFixture SERVER_FIXTURE;

  private NPTestContainerInstances()
  {

  }

  public static int serverDatabasePort()
  {
    return 15432;
  }

  public static int idstoreDatabasePort()
  {
    return 55432;
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

  public static NPTestContainers.NPDatabaseFixture database(
    final EContainerSupervisorType supervisor)
    throws Exception
  {
    if (DATABASE_FIXTURE == null) {
      DATABASE_FIXTURE =
        NPTestContainers.createDatabase(supervisor, serverDatabasePort());
    }
    DATABASE_FIXTURE.reset();
    return DATABASE_FIXTURE;
  }

  public static NPTestContainers.NPIdstoreFixture idstore(
    final EContainerSupervisorType supervisor)
    throws Exception
  {
    if (IDSTORE_FIXTURE == null) {
      IDSTORE_FIXTURE =
        NPTestContainers.createIdstore(
          supervisor,
          Files.createTempDirectory("northpike-idstore"),
          idstoreDatabasePort(),
          idstoreAdminPort(),
          idstoreUserPort(),
          idstoreUserViewPort()
        );
    }

    IDSTORE_FIXTURE.reset();
    return IDSTORE_FIXTURE;
  }

  public static NPTestContainers.NPServerFixture server(
    final EContainerSupervisorType containers)
    throws Exception
  {
    if (SERVER_FIXTURE == null) {
      SERVER_FIXTURE = NPTestContainers.createServer(
        idstore(containers),
        database(containers),
        Files.createTempDirectory("northpike-server"),
        serverAgentPort(),
        serverUserPort(),
        serverArchivePort()
      );
    }
    return SERVER_FIXTURE;
  }

  private static int serverArchivePort()
  {
    return 40002;
  }

  private static int serverUserPort()
  {
    return 40001;
  }

  private static int serverAgentPort()
  {
    return 40000;
  }
}
