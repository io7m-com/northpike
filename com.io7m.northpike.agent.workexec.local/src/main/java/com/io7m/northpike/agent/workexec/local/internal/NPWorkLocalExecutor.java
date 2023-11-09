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


package com.io7m.northpike.agent.workexec.local.internal;

import com.io7m.northpike.agent.workexec.api.NPAWorkExecutionType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorType;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;

/**
 * An executor that executes work on the local system.
 */

public final class NPWorkLocalExecutor implements NPAWorkExecutorType
{
  private final RPServiceDirectoryType services;
  private final NPAWorkExecutorConfiguration configuration;
  private final AtomicBoolean closed;

  /**
   * An executor that executes work on the local system.
   *
   * @param inServices      The service directory
   * @param inConfiguration The configuration
   */

  public NPWorkLocalExecutor(
    final RPServiceDirectoryType inServices,
    final NPAWorkExecutorConfiguration inConfiguration)
  {
    this.services =
      Objects.requireNonNull(inServices, "services");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.closed =
      new AtomicBoolean(false);
  }

  @Override
  public Map<String, String> environment()
  {
    return System.getenv();
  }

  @Override
  public Map<String, String> systemProperties()
  {
    return System.getProperties()
      .entrySet()
      .stream()
      .map(e -> Map.entry(e.getKey().toString(), e.getValue().toString()))
      .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
  }

  @Override
  public NPAWorkExecutionType createExecution(
    final NPAgentWorkItem workItem)
  {
    return NPWorkLocalExecution.create(
      this.services,
      this.configuration,
      workItem
    );
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public void close()
  {
    if (this.closed.compareAndSet(false, true)) {
      // Nothing at the moment
    }
  }
}
