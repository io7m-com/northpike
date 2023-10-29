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

import com.io7m.jattribute.core.AttributeType;
import com.io7m.jattribute.core.Attributes;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.api.NPAgentType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.strings.NPStrings;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * A basic agent.
 */

public final class NPAgent implements NPAgentType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgent.class);

  private final AtomicBoolean closed;
  private final CloseableCollectionType<NPAgentException> resources;
  private final HashSet<NPAgentTaskType> tasks;
  private final AttributeType<NPAgentConfiguration> configurationAttribute;
  private final AtomicBoolean started;

  private NPAgent(
    final CloseableCollectionType<NPAgentException> inResources,
    final HashSet<NPAgentTaskType> inTasks,
    final AttributeType<NPAgentConfiguration> inConfiguration)
  {
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.tasks =
      Objects.requireNonNull(inTasks, "tasks");
    this.configurationAttribute =
      Objects.requireNonNull(inConfiguration, "configurationAttribute");
    this.closed =
      new AtomicBoolean(false);
    this.started =
      new AtomicBoolean(false);
  }

  /**
   * A basic agent.
   *
   * @param strings       The strings
   * @param configuration The configuration
   *
   * @return An agent
   *
   * @throws InterruptedException On interruption
   */

  public static NPAgentType open(
    final NPStrings strings,
    final NPAgentConfiguration configuration)
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

    final var attributes =
      Attributes.create(throwable -> LOG.error("", throwable));
    final var configurationAttribute =
      attributes.create(configuration);

    final var tasks = new HashSet<NPAgentTaskType>();
    tasks.add(
      resources.add(NPAgentTaskMessaging.open(strings, configurationAttribute)));
    tasks.add(
      resources.add(NPAgentTaskWorkController.open(strings, configurationAttribute)));

    return new NPAgent(resources, tasks, configurationAttribute);
  }

  @Override
  public void start()
    throws InterruptedException, TimeoutException
  {
    if (this.started.compareAndSet(false, true)) {
      LOG.debug("Start");

      final var latch = new CountDownLatch(this.tasks.size());
      for (final var task : this.tasks) {
        Thread.ofVirtual()
          .name("%s.".formatted(task.name()), 0L)
          .start(() -> {
            latch.countDown();
            task.run();
          });
      }

      if (!latch.await(5L, TimeUnit.SECONDS)) {
        throw new TimeoutException("Timed out waiting for agent startup.");
      }
    }
  }

  @Override
  public void setConfiguration(
    final NPAgentConfiguration agentConfiguration)
  {
    this.configurationAttribute.set(agentConfiguration);
  }

  @Override
  public void close()
    throws NPAgentException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }
}
