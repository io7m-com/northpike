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


package com.io7m.northpike.tests.server.agents;

import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPKey;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.protocol.agent.NPACommandCEnvironmentInfo;
import com.io7m.northpike.server.internal.agents.NPACmdEnvironmentInfo;
import com.io7m.northpike.server.internal.agents.NPAgentCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;

/**
 * Tests for a command.
 */

public final class NPACmdEnvironmentInfoTest
{
  private NPAgentCommandContextType context;

  @BeforeEach
  public void setup()
  {
    this.context =
      Mockito.mock(NPAgentCommandContextType.class);

    Mockito.doAnswer(invocationOnMock -> {
      final var message =
        invocationOnMock.getArgument(0, NPStringConstantType.class);
      final var errorCode =
        invocationOnMock.getArgument(1, NPErrorCode.class);

      return new NPException(
        message.toString(),
        errorCode,
        Map.of(),
        Optional.empty()
      );
    }).when(this.context).fail(any(), any());
  }

  /**
   * Requires authentication.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure0()
    throws Exception
  {
    final var handler = new NPACmdEnvironmentInfo();

    Mockito.when(this.context.onAuthenticationRequire())
      .thenThrow(new NPPlanException(
        ERROR_AUTHENTICATION.name(),
        errorAuthentication(),
        Map.of(),
        Optional.empty()
      ));

    final var command =
      new NPACommandCEnvironmentInfo(
        UUID.randomUUID(),
        Map.ofEntries(
          Map.entry("ek0", "ev0"),
          Map.entry("ek1", "ev1"),
          Map.entry("ek2", "ev2")
        ),
        Map.ofEntries(
          Map.entry("spk0", "spv0"),
          Map.entry("spk1", "spv1"),
          Map.entry("spk2", "spv2")
        )
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Requires an agent that exists.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure1()
    throws Exception
  {
    final var handler = new NPACmdEnvironmentInfo();

    final var agentId =
      NPAgentID.of("ab27f114-6b29-5ab2-a528-b41ef98abe76");

    Mockito.when(this.context.onAuthenticationRequire())
      .thenReturn(agentId);
    Mockito.when(this.context.agentFindForId(any()))
      .thenReturn(Optional.empty());

    final var command =
      new NPACommandCEnvironmentInfo(
        UUID.randomUUID(),
        Map.ofEntries(
          Map.entry("ek0", "ev0"),
          Map.entry("ek1", "ev1"),
          Map.entry("ek2", "ev2")
        ),
        Map.ofEntries(
          Map.entry("spk0", "spv0"),
          Map.entry("spk1", "spv1"),
          Map.entry("spk2", "spv2")
        )
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_NONEXISTENT", ex.message());
    assertEquals(errorNonexistent(), ex.errorCode());
  }

  /**
   * Succeeds if authenticated.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSuccess0()
    throws Exception
  {
    final var handler = new NPACmdEnvironmentInfo();

    final var command =
      new NPACommandCEnvironmentInfo(
        UUID.randomUUID(),
        Map.ofEntries(
          Map.entry("ek0", "ev0"),
          Map.entry("ek1", "ev1"),
          Map.entry("ek2", "ev2")
        ),
        Map.ofEntries(
          Map.entry("spk0", "spv0"),
          Map.entry("spk1", "spv1"),
          Map.entry("spk2", "spv2")
        )
      );

    final var key = NPKey.generate();
    Mockito.when(this.context.agentFindForId(any()))
      .thenReturn(Optional.of(
        new NPAgentDescription(
          NPAgentID.of("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
          "Agent",
          key,
          Map.of(),
          Map.of(),
          Map.of()
        )
      ));

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());

    Mockito.verify(this.context)
      .agentUpdate(
        new NPAgentDescription(
          NPAgentID.of("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
          "Agent",
          key,
          Map.ofEntries(
            Map.entry("ek0", "ev0"),
            Map.entry("ek1", "ev1"),
            Map.entry("ek2", "ev2")
          ),
          Map.ofEntries(
            Map.entry("spk0", "spv0"),
            Map.entry("spk1", "spv1"),
            Map.entry("spk2", "spv2")
          ),
          Map.of()
        )
      );
  }
}
