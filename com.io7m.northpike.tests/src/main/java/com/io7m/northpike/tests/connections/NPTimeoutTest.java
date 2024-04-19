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


package com.io7m.northpike.tests.connections;

import com.io7m.northpike.connections.NPTimeout;
import org.junit.jupiter.api.Test;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertThrows;

public final class NPTimeoutTest
{
  @Test
  public void testTimeoutNotCancelled()
  {
    assertThrows(InterruptedException.class, () -> {
      NPTimeout.create(Thread.currentThread(), Duration.ofSeconds(1L));
      Thread.sleep(Duration.ofSeconds(10L));
    });
  }

  @Test
  public void testTimeoutCancelled()
    throws Exception
  {
    final var timeout =
      NPTimeout.create(Thread.currentThread(), Duration.ofSeconds(5L));

    Thread.sleep(1_000L);
    timeout.close();
  }
}
