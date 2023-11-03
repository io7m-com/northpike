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


package com.io7m.northpike.agent;

import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.api.NPAgentHostConfiguration;
import com.io7m.northpike.agent.api.NPAgentHostFactoryType;
import com.io7m.northpike.agent.api.NPAgentHostType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseFactoryType;
import com.io7m.northpike.agent.internal.NPAgentHost;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorFactoryType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceFactoryType;

import java.util.List;
import java.util.Objects;
import java.util.ServiceLoader;

/**
 * A factory of agent hosts.
 */

public final class NPAgentHosts implements NPAgentHostFactoryType
{
  private final List<NPAgentDatabaseFactoryType> databases;
  private final List<NPTelemetryServiceFactoryType> telemetry;
  private final List<NPAWorkExecutorFactoryType> workExecutors;

  /**
   * A factory of agent hosts.
   */

  public NPAgentHosts()
  {
    this(
      ServiceLoader.load(NPAgentDatabaseFactoryType.class)
        .stream()
        .map(ServiceLoader.Provider::get)
        .toList(),
      ServiceLoader.load(NPTelemetryServiceFactoryType.class)
        .stream()
        .map(ServiceLoader.Provider::get)
        .toList(),
      ServiceLoader.load(NPAWorkExecutorFactoryType.class)
        .stream()
        .map(ServiceLoader.Provider::get)
        .toList()
    );
  }

  /**
   * A factory of agent hosts.
   *
   * @param inDatabases     A set of database factories
   * @param inTelemetry     A set of telemetry factories
   * @param inWorkExecutors A set of work executor factories
   */

  public NPAgentHosts(
    final List<NPAgentDatabaseFactoryType> inDatabases,
    final List<NPTelemetryServiceFactoryType> inTelemetry,
    final List<NPAWorkExecutorFactoryType> inWorkExecutors)
  {
    this.databases =
      Objects.requireNonNull(inDatabases, "databases");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.workExecutors =
      Objects.requireNonNull(inWorkExecutors, "workExecutors");
  }

  @Override
  public NPAgentHostType createHost(
    final NPAgentHostConfiguration configuration)
    throws NPAgentException
  {
    return NPAgentHost.open(
      this.databases,
      this.telemetry,
      this.workExecutors,
      configuration
    );
  }

  @Override
  public String toString()
  {
    return "[NPAgentHosts 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }
}
