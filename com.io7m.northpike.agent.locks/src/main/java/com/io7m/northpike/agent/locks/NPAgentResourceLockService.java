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


package com.io7m.northpike.agent.locks;

import com.io7m.jaffirm.core.Preconditions;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentResourceName;

import java.math.BigInteger;
import java.time.Duration;
import java.time.OffsetDateTime;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;

import static java.math.BigInteger.ONE;

/**
 * The agent lock service.
 */

public final class NPAgentResourceLockService
  implements NPAgentResourceLockServiceType
{
  private final Object resourcesMonitor;
  private final ConcurrentHashMap<NPAgentResourceName, NPAgentLockCount> resourceLocks;

  private NPAgentResourceLockService()
  {
    this.resourcesMonitor =
      new Object();
    this.resourceLocks =
      new ConcurrentHashMap<>();
  }

  /**
   * @return A new agent lock service.
   */

  public static NPAgentResourceLockServiceType create()
  {
    return new NPAgentResourceLockService();
  }

  @Override
  public String toString()
  {
    return "[NPAgentResourceLockService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }

  @Override
  public Duration lockTimeoutDefault()
  {
    return Duration.ofHours(1L);
  }

  @Override
  public NPAgentResourceLockSetType lock(
    final NPAgentLocalName agent,
    final Set<NPAgentResourceName> resources,
    final Duration timeout)
    throws TimeoutException, InterruptedException
  {
    Objects.requireNonNull(agent, "agent");
    Objects.requireNonNull(resources, "resources");
    Objects.requireNonNull(timeout, "timeout");

    final var timeStart = OffsetDateTime.now();
    while (true) {
      try {
        return this.tryLock(agent, resources);
      } catch (final NPAgentResourcesAreLocked e) {
        // Pause and retry
      }

      final var timeNow = OffsetDateTime.now();
      if (timeNow.isAfter(timeStart.plus(timeout))) {
        throw new TimeoutException();
      }
      Thread.sleep(1L);
    }
  }

  @Override
  public boolean isLockedBy(
    final NPAgentLocalName agent,
    final NPAgentResourceName resource)
  {
    Objects.requireNonNull(agent, "agent");
    Objects.requireNonNull(resource, "resource");

    final var holder = this.resourceLocks.get(resource);
    if (holder != null) {
      return Objects.equals(holder.agent, agent);
    }
    return false;
  }

  private void unlock(
    final NPAgentLocalName agent,
    final Set<NPAgentResourceName> resourcesToUnlock)
  {
    synchronized (this.resourcesMonitor) {

      /*
       * For safety reasons, we'll verify that all resources claimed to be
       * held by the agent actually _are_ held.
       */

      for (final var resource : resourcesToUnlock) {
        final var existingHolder = this.resourceLocks.get(resource);
        if (existingHolder == null) {
          throw new IllegalStateException(
            "Resource %s is not held by agent %s (or any other agent)"
              .formatted(resource, agent)
          );
        }

        if (!existingHolder.agent.equals(agent)) {
          throw new IllegalStateException(
            "Resource %s is not held by agent %s (but is held by agent %s)"
              .formatted(resource, agent, existingHolder.agent)
          );
        }
      }

      /*
       * Now we'll decrement lock counts, or remove locks entirely.
       */

      for (final var resource : resourcesToUnlock) {
        final var existingHolder = this.resourceLocks.get(resource);
        if (existingHolder.count.equals(ONE)) {
          this.resourceLocks.remove(resource);
        } else {
          this.resourceLocks.put(
            resource,
            new NPAgentLockCount(
              existingHolder.agent,
              existingHolder.count.subtract(ONE)
            )
          );
        }
      }
    }
  }

  private NPAgentResourceLockSetType tryLock(
    final NPAgentLocalName agent,
    final Set<NPAgentResourceName> resourcesToLock)
    throws NPAgentResourcesAreLocked
  {
    synchronized (this.resourcesMonitor) {

      /*
       * If any of the resources are held by a different agent, then locking
       * fails fast without affecting any resource.
       */

      for (final var resource : resourcesToLock) {
        final var existingHolder = this.resourceLocks.get(resource);
        if (existingHolder != null) {
          if (!existingHolder.agent.equals(agent)) {
            throw new NPAgentResourcesAreLocked();
          }
        }
      }

      /*
       * At this point, all the resources are either not held, or are
       * held by the same agent. We create locks for the resources that aren't
       * held, and increment lock counts for those that are.
       */

      for (final var resource : resourcesToLock) {
        final var existingHolder = this.resourceLocks.get(resource);

        final NPAgentLockCount holder;
        if (existingHolder != null) {
          holder = new NPAgentLockCount(agent, existingHolder.count.add(ONE));
        } else {
          holder = new NPAgentLockCount(agent, ONE);
        }

        this.resourceLocks.put(resource, holder);
      }

      return new NPAgentResourceSet(
        this,
        agent,
        Set.copyOf(resourcesToLock)
      );
    }
  }

  @Override
  public String description()
  {
    return "Agent resource locking service";
  }

  private record NPAgentLockCount(
    NPAgentLocalName agent,
    BigInteger count)
  {
    NPAgentLockCount
    {
      Objects.requireNonNull(agent, "agent");
      Objects.requireNonNull(count, "count");

      Preconditions.checkPrecondition(
        count.compareTo(BigInteger.ZERO) > 0,
        "Counts must be positive"
      );
    }
  }

  private static final class NPAgentResourcesAreLocked
    extends Exception
  {
    NPAgentResourcesAreLocked()
    {

    }
  }

  private static final class NPAgentResourceSet
    implements NPAgentResourceLockSetType
  {
    private final NPAgentResourceLockService service;
    private final NPAgentLocalName agent;
    private final Set<NPAgentResourceName> resources;
    private final AtomicBoolean closed;

    NPAgentResourceSet(
      final NPAgentResourceLockService inService,
      final NPAgentLocalName inAgent,
      final Set<NPAgentResourceName> inResources)
    {
      this.service =
        Objects.requireNonNull(inService, "service");
      this.agent =
        Objects.requireNonNull(inAgent, "agent");
      this.resources =
        Set.copyOf(inResources);
      this.closed =
        new AtomicBoolean(false);
    }

    @Override
    public void close()
    {
      if (this.closed.compareAndSet(false, true)) {
        this.service.unlock(this.agent, this.resources);
      }
    }
  }
}
