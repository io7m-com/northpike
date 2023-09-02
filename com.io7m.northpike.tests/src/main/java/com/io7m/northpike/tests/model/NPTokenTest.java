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


package com.io7m.northpike.tests.model;

import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.model.NPValidityException;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

public final class NPTokenTest
{
  @Test
  public void testParse0()
  {
    final var v0 =
      new NPToken("96b453638a7c1b254bb3ffbc4a315d7b1090641a451a58167a256977bec982cd");
    final var v1 =
      new NPToken("96b453638a7c1b254bb3ffbc4a315d7b1090641a451a58167a256977bec982cd");

    assertEquals(v0, v1);
    assertEquals("96b453638a7c1b254bb3ffbc4a315d7b1090641a451a58167a256977bec982cd", v0.toString());
    assertEquals(0, v0.compareTo(v1));
  }

  @Test
  public void testParse1()
  {
    assertThrows(NPValidityException.class, () -> {
      new NPToken("96");
    });
  }
}
