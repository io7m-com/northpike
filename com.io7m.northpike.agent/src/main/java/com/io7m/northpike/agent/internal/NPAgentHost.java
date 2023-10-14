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

import com.io7m.northpike.agent.api.NPAgentHostConfiguration;
import com.io7m.northpike.agent.api.NPAgentHostType;

import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The basic agent host.
 */

public final class NPAgentHost implements NPAgentHostType
{
  private final NPAgentHostConfiguration configuration;
  private final AtomicBoolean closed;

  /**
   * The basic agent host.
   *
   * @param inConfiguration The host configuration
   */

  public NPAgentHost(
    final NPAgentHostConfiguration inConfiguration)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.closed =
      new AtomicBoolean(true);
  }

  @Override
  public void start()
  {
    if (this.closed.compareAndSet(true, false)) {
      // Nothing yet
    }
  }

  @Override
  public void stop()
  {
    if (this.closed.compareAndSet(false, true)) {
      // Nothing yet
    }
  }

  @Override
  public void close()
  {
    if (this.closed.compareAndSet(false, true)) {
      // Nothing yet
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }
}
