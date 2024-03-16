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


package com.io7m.northpike.tests.agent.lock;

import com.io7m.northpike.agent.locks.NPAgentResourceLockService;
import com.io7m.northpike.agent.locks.NPAgentResourceLockServiceType;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentResourceName;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.Set;
import java.util.concurrent.TimeoutException;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class NPAgentResourceLockServiceTest
{
  public static final Duration ONESEC = Duration.ofSeconds(1L);
  private NPAgentResourceLockServiceType locks;

  @BeforeEach
  public void setup()
  {
    this.locks = NPAgentResourceLockService.create();
  }

  @Test
  public void testLockUncontended0()
    throws Exception
  {
    final var agent0 =
      NPAgentLocalName.of("agent0");
    final var res0 =
      NPAgentResourceName.of("res0");
    final var res1 =
      NPAgentResourceName.of("res1");
    final var res2 =
      NPAgentResourceName.of("res2");

    assertFalse(this.locks.isLockedBy(agent0, res0));
    assertFalse(this.locks.isLockedBy(agent0, res1));
    assertFalse(this.locks.isLockedBy(agent0, res2));

    try (var set = this.locks.lock(agent0, Set.of(res0, res1, res2), ONESEC)) {
      assertTrue(this.locks.isLockedBy(agent0, res0));
      assertTrue(this.locks.isLockedBy(agent0, res1));
      assertTrue(this.locks.isLockedBy(agent0, res2));
    }

    assertFalse(this.locks.isLockedBy(agent0, res0));
    assertFalse(this.locks.isLockedBy(agent0, res1));
    assertFalse(this.locks.isLockedBy(agent0, res2));

    try (var set = this.locks.lock(agent0, Set.of(res0, res1, res2), ONESEC)) {
      assertTrue(this.locks.isLockedBy(agent0, res0));
      assertTrue(this.locks.isLockedBy(agent0, res1));
      assertTrue(this.locks.isLockedBy(agent0, res2));
    }

    assertFalse(this.locks.isLockedBy(agent0, res0));
    assertFalse(this.locks.isLockedBy(agent0, res1));
    assertFalse(this.locks.isLockedBy(agent0, res2));
  }

  @Test
  public void testLockUncontended1()
    throws Exception
  {
    final var agentName =
      NPAgentLocalName.of("agent0");
    final var res0 =
      NPAgentResourceName.of("res0");
    final var res1 =
      NPAgentResourceName.of("res1");
    final var res2 =
      NPAgentResourceName.of("res2");

    assertFalse(this.locks.isLockedBy(agentName, res0));
    assertFalse(this.locks.isLockedBy(agentName, res1));
    assertFalse(this.locks.isLockedBy(agentName, res2));

    try (var set0 =
           this.locks.lock(agentName, Set.of(res0, res1, res2), ONESEC)) {
      assertTrue(this.locks.isLockedBy(agentName, res0));
      assertTrue(this.locks.isLockedBy(agentName, res1));
      assertTrue(this.locks.isLockedBy(agentName, res2));

      try (var set1 =
             this.locks.lock(agentName, Set.of(res0, res1, res2), ONESEC)) {
        assertTrue(this.locks.isLockedBy(agentName, res0));
        assertTrue(this.locks.isLockedBy(agentName, res1));
        assertTrue(this.locks.isLockedBy(agentName, res2));
      }
    }

    assertFalse(this.locks.isLockedBy(agentName, res0));
    assertFalse(this.locks.isLockedBy(agentName, res1));
    assertFalse(this.locks.isLockedBy(agentName, res2));
  }

  @Test
  public void testLockContended0()
    throws Exception
  {
    final var agent0 =
      NPAgentLocalName.of("agent0");
    final var agent1 =
      NPAgentLocalName.of("agent1");
    final var res0 =
      NPAgentResourceName.of("res0");

    assertFalse(this.locks.isLockedBy(agent0, res0));
    assertFalse(this.locks.isLockedBy(agent1, res0));

    try (var set0 = this.locks.lock(agent0, Set.of(res0), ONESEC)) {
      assertTrue(this.locks.isLockedBy(agent0, res0));
      assertThrows(TimeoutException.class, () -> {
        try (var set1 = this.locks.lock(agent1, Set.of(res0), ONESEC)) {
          assertFalse(this.locks.isLockedBy(agent1, res0));
        }
      });
    }

    assertFalse(this.locks.isLockedBy(agent0, res0));
    assertFalse(this.locks.isLockedBy(agent1, res0));
  }
}
