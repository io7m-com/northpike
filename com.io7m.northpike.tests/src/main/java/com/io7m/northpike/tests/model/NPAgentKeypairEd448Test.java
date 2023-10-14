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

import com.io7m.northpike.model.NPSignedData;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPairType;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.security.SecureRandom;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class NPAgentKeypairEd448Test
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentKeypairEd448Test.class);

  private NPAgentKeyPairFactoryEd448 keyFactory;

  @BeforeEach
  public void setup()
  {
    this.keyFactory = new NPAgentKeyPairFactoryEd448();
  }

  @RepeatedTest(value = 10)
  public void testEncodeDecodeSignVerify()
    throws Exception
  {
    final var rng =
      SecureRandom.getInstanceStrong();
    final var output =
      new ByteArrayOutputStream();
    final var original =
      this.keyFactory.generateKeyPair();

    final var data = new byte[128];
    rng.nextBytes(data);

    original.encodeToStream(output);
    output.flush();

    final NPAgentKeyPairType decoded;
    try (var input = new ByteArrayInputStream(output.toByteArray())) {
      decoded = this.keyFactory.parseFromStream(input);
      LOG.debug("EXPECTED: {}", original.id());
      LOG.debug("RECEIVED: {}", decoded.id());
      assertEquals(original.id(), decoded.id());
    }

    final var signed = new NPSignedData(data, original.signData(data));
    assertTrue(original.verifyData(signed));
    assertTrue(decoded.verifyData(signed));
  }
}
