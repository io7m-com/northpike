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


package com.io7m.northpike.toolexecj.runner;

import com.io7m.northpike.toolexecj.runner.internal.NPTJRunner;

import java.math.BigInteger;
import java.util.Map;

/**
 * The main runner service.
 */

public final class NPTJRunners implements NPTJRunnerServiceType
{
  private static final Object EXECUTION_ID_LOCK = new Object();
  private static BigInteger EXECUTION_ID = BigInteger.ZERO;

  private NPTJRunners()
  {

  }

  /**
   * @return A new runner service.
   */

  public static NPTJRunnerServiceType create()
  {
    return new NPTJRunners();
  }

  private static BigInteger freshId()
  {
    synchronized (EXECUTION_ID_LOCK) {
      final var now = EXECUTION_ID;
      EXECUTION_ID = EXECUTION_ID.add(BigInteger.ONE);
      return now;
    }
  }

  @Override
  public String description()
  {
    return "Toolexec/JS runner service.";
  }

  @Override
  public NPTJRunnerType create(
    final Map<String, String> initialEnvironment,
    final String program)
  {
    return new NPTJRunner(
      freshId(),
      initialEnvironment,
      program
    );
  }
}
