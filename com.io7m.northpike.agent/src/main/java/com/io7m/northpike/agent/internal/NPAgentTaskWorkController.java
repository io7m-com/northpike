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


package com.io7m.northpike.agent.internal;

import com.io7m.jattribute.core.AttributeReadableType;
import com.io7m.jattribute.core.AttributeType;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.strings.NPStrings;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The task that handles work for the agent.
 */

public final class NPAgentTaskWorkController implements NPAgentTaskType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentTaskWorkController.class);

  private final AtomicBoolean closed;
  private final NPStrings strings;
  private final CloseableCollectionType<NPAgentException> resources;
  private final AttributeReadableType<NPAgentConfiguration> configuration;

  private NPAgentTaskWorkController(
    final AttributeReadableType<NPAgentConfiguration> inConfiguration,
    final NPStrings inStrings,
    final CloseableCollectionType<NPAgentException> inResources)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.closed =
      new AtomicBoolean(false);
  }

  /**
   * The task that handles messaging for the agent.
   *
   * @param strings       The strings
   * @param configuration The configuration
   *
   * @return An agent
   *
   * @throws InterruptedException On interruption
   */

  public static NPAgentTaskWorkController open(
    final NPStrings strings,
    final AttributeType<NPAgentConfiguration> configuration)
    throws InterruptedException
  {
    Objects.requireNonNull(strings, "strings");
    Objects.requireNonNull(configuration, "configuration");

    final var resources =
      CloseableCollection.create(() -> new NPAgentException(
        "One or more resources could not be closed.",
        new NPErrorCode("resources"),
        Map.of(),
        Optional.empty()
      ));

    final var task =
      new NPAgentTaskWorkController(configuration, strings, resources);

    resources.add(configuration.subscribe(task::onConfigurationUpdated));
    return task;
  }

  private void onConfigurationUpdated(
    final NPAgentConfiguration oldValue,
    final NPAgentConfiguration newValue)
  {

  }

  @Override
  public void run()
  {
    LOG.debug("Start");

    while (!this.isClosed()) {
      try {
        Thread.sleep(1_000L);
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
      }
    }
  }

  @Override
  public void close()
    throws NPAgentException
  {
    if (this.closed.compareAndSet(false, true)) {
      LOG.debug("Close");
      this.resources.close();
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public String name()
  {
    return "com.io7m.northpike.agent.work_controller";
  }
}
