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
import com.io7m.ervilla.api.EContainerType;
import com.io7m.ervilla.postgres.EPgSpecs;
import com.io7m.northpike.tests.NPTestProperties;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Objects;
import java.util.Optional;

/**
 * A PostgreSQL fixture.
 */

public final class NPPostgresFixture
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPIdstoreFixture.class);

  private final EContainerType container;
  private final String databaseOwner;
  private final String primaryIp;
  private final int port;

  private NPPostgresFixture(
    final EContainerType inContainer,
    final String inDatabaseOwner,
    final String inPrimaryIp,
    final int inPort)
  {
    this.container =
      Objects.requireNonNull(inContainer, "container");
    this.databaseOwner =
      Objects.requireNonNull(inDatabaseOwner, "databaseOwner");
    this.primaryIp =
      Objects.requireNonNull(inPrimaryIp, "primaryIp");
    this.port =
      inPort;
  }

  public static NPPostgresFixture create(
    final EContainerSupervisorType supervisor,
    final String primaryIp,
    final int port)
    throws Exception
  {
    LOG.info(
      "Creating postgres database on {}:{}", primaryIp, Integer.valueOf(port));

    return new NPPostgresFixture(
      supervisor.start(
        EPgSpecs.builderFromDockerIO(
          NPTestProperties.POSTGRESQL_VERSION,
          Optional.of(primaryIp),
          port,
          "postgres",
          "postgres",
          "12345678"
        ).build()
      ),
      "postgres",
      primaryIp,
      port
    );
  }

  public String primaryIP()
  {
    return this.primaryIp;
  }

  public EContainerType container()
  {
    return this.container;
  }

  public String databaseOwner()
  {
    return this.databaseOwner;
  }

  public int port()
  {
    return this.port;
  }
}
