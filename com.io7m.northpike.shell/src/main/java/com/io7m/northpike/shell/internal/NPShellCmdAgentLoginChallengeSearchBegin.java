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

package com.io7m.northpike.shell.internal;

import com.io7m.idstore.model.IdTimeRange;
import com.io7m.northpike.model.NPTimeRange;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeSearchParameters;
import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeSearchBegin;
import com.io7m.northpike.protocol.user.NPUResponseAgentLoginChallengeSearch;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.time.OffsetDateTime;
import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "agent-login-challenge-search-begin"
 */

public final class NPShellCmdAgentLoginChallengeSearchBegin
  extends NPShellCmdAbstractCR<NPUCommandAgentLoginChallengeSearchBegin, NPUResponseAgentLoginChallengeSearch>
{
  private static final QParameterNamed1<OffsetDateTime> TIME_FROM =
    new QParameterNamed1<>(
      "--time-from",
      List.of(),
      new QConstant("Return login challenge records later than this date."),
      Optional.of(IdTimeRange.largest().timeLower()),
      OffsetDateTime.class
    );

  private static final QParameterNamed1<OffsetDateTime> TIME_TO =
    new QParameterNamed1<>(
      "--time-to",
      List.of(),
      new QConstant("Return login challenge records earlier than this date."),
      Optional.of(IdTimeRange.largest().timeUpper()),
      OffsetDateTime.class
    );

  private static final QParameterNamed1<Integer> LIMIT =
    new QParameterNamed1<>(
      "--limit",
      List.of(),
      new QConstant("The maximum number of results per page."),
      Optional.of(Integer.valueOf(10)),
      Integer.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAgentLoginChallengeSearchBegin(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "agent-login-challenge-search-begin",
        new QConstant("Begin searching for agent login challenge records."),
        Optional.empty()
      ),
      NPUCommandAgentLoginChallengeSearchBegin.class,
      NPUResponseAgentLoginChallengeSearch.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      LIMIT,
      TIME_FROM,
      TIME_TO
    );
  }

  @Override
  protected NPUCommandAgentLoginChallengeSearchBegin onCreateCommand(
    final QCommandContextType context)
  {
    final var parameters =
      new NPAgentLoginChallengeSearchParameters(
        new NPTimeRange(
          context.parameterValue(TIME_FROM),
          context.parameterValue(TIME_TO)
        ),
        context.parameterValue(LIMIT).longValue()
      );

    return new NPUCommandAgentLoginChallengeSearchBegin(UUID.randomUUID(), parameters);
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseAgentLoginChallengeSearch response)
    throws Exception
  {
    this.formatter().formatAgentLoginChallenges(response.results());
  }
}
