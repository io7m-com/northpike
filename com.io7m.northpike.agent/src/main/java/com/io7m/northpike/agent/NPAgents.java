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

import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentFactoryType;
import com.io7m.northpike.agent.api.NPAgentType;
import com.io7m.northpike.agent.internal.NPAgent;
import com.io7m.northpike.strings.NPStrings;

import java.util.Locale;
import java.util.Objects;

/**
 * A factory of agents.
 */

public final class NPAgents implements NPAgentFactoryType
{
  private final NPStrings strings;

  /**
   * A factory of agents.
   */

  public NPAgents()
  {
    this(Locale.getDefault());
  }

  /**
   * A factory of agents.
   *
   * @param locale The locale for string resources
   */

  public NPAgents(
    final Locale locale)
  {
    this(NPStrings.create(locale));
  }

  /**
   * A factory of agents.
   *
   * @param inStrings The string resources
   */

  public NPAgents(
    final NPStrings inStrings)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "inStrings");
  }

  @Override
  public NPAgentType createAgent(
    final NPAgentConfiguration configuration)
    throws InterruptedException
  {
    return NPAgent.open(this.strings, configuration);
  }
}
