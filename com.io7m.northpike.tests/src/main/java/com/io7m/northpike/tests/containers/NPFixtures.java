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

import com.io7m.ervilla.api.EContainerPodType;
import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.ervilla.api.EPortAddressType;
import com.io7m.ervilla.api.EPortProtocol;
import com.io7m.ervilla.api.EPortPublish;
import com.io7m.northpike.tests.server.assignments.NPAssignmentFixture;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

public final class NPFixtures
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPFixtures.class);

  private static final Path BASE_DIRECTORY;
  private static final List<EPortPublish> PUBLICATION_PORTS;
  private static EContainerPodType POD;
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

    PUBLICATION_PORTS =
      List.of(
        new EPortPublish(
          new EPortAddressType.All(),
          webServerPort(),
          webServerPort(),
          EPortProtocol.TCP
        ),
        new EPortPublish(
          new EPortAddressType.All(),
          postgresPort(),
          postgresPort(),
          EPortProtocol.TCP
        ),
        new EPortPublish(
          new EPortAddressType.All(),
          idstoreAdminPort(),
          idstoreAdminPort(),
          EPortProtocol.TCP
        ),
        new EPortPublish(
          new EPortAddressType.All(),
          idstoreUserPort(),
          idstoreUserPort(),
          EPortProtocol.TCP
        ),
        new EPortPublish(
          new EPortAddressType.All(),
          idstoreUserViewPort(),
          idstoreUserViewPort(),
          EPortProtocol.TCP
        )
      );
  }

  private NPFixtures()
  {

  }

  public static int webServerPort()
  {
    return 20000;
  }

  public static int postgresPort()
  {
    return 5432;
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

  public static int northpikeArchivePort()
  {
    return 40002;
  }

  public static int northpikeUserPort()
  {
    return 40001;
  }

  public static int northpikeAgentAPIPort()
  {
    return 40000;
  }

  public static EContainerPodType pod(
    final EContainerSupervisorType supervisor)
    throws Exception
  {
    if (POD == null) {
      POD = supervisor.createPod(PUBLICATION_PORTS);
    } else {
      LOG.info("Reusing pod {}.", POD.name());
    }
    return POD;
  }

  public static NPDatabaseFixture database(
    final EContainerPodType containerFactory)
    throws Exception
  {
    if (DATABASE_FIXTURE == null) {
      DATABASE_FIXTURE =
        NPDatabaseFixture.create(
          postgres(containerFactory)
        );
    } else {
      LOG.info("Reusing northpike database fixture.");
    }
    return DATABASE_FIXTURE;
  }

  public static NPPostgresFixture postgres(
    final EContainerPodType containerFactory)
    throws Exception
  {
    if (POSTGRES_FIXTURE == null) {
      POSTGRES_FIXTURE =
        NPPostgresFixture.create(
          containerFactory,
          postgresPort()
        );
    } else {
      LOG.info("Reusing postgres fixture.");
    }
    return POSTGRES_FIXTURE;
  }

  public static NPIdstoreFixture idstore(
    final EContainerPodType containerFactory)
    throws Exception
  {
    if (IDSTORE_FIXTURE == null) {
      IDSTORE_FIXTURE =
        NPIdstoreFixture.create(
          containerFactory,
          postgres(containerFactory),
          BASE_DIRECTORY,
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
    final EContainerPodType containerFactory)
    throws Exception
  {
    if (SERVER_FIXTURE == null) {
      SERVER_FIXTURE =
        NPServerFixture.create(
          idstore(containerFactory),
          database(containerFactory),
          BASE_DIRECTORY,
          northpikeAgentAPIPort(),
          northpikeUserPort(),
          northpikeArchivePort()
        );
    } else {
      LOG.info("Reusing northpike server fixture.");
    }
    return SERVER_FIXTURE;
  }

  public static NPAssignmentFixture assignment(
    final EContainerPodType containerFactory)
    throws Exception
  {
    if (ASSIGNMENT_FIXTURE == null) {
      ASSIGNMENT_FIXTURE =
        NPAssignmentFixture.create(
          idstore(containerFactory),
          database(containerFactory),
          BASE_DIRECTORY.resolve("repositories")
        );
    }
    return ASSIGNMENT_FIXTURE;
  }
}
