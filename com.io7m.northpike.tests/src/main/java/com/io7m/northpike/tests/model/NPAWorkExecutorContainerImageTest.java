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


package com.io7m.northpike.tests.model;

import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorContainerImage;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class NPAWorkExecutorContainerImageTest
{
  @Test
  public void testWithHash0()
  {
    final var c =
      NPAWorkExecutorContainerImage.of("quay.io/io7mcom/idstore:1.0.0@sha256:75796f97f4b5b51e7f6bec3673ba442b85cb6486bf737a37ce51d90266b4e176");

    assertEquals("quay.io", c.registry());
    assertEquals("io7mcom/idstore", c.name());
    assertEquals("1.0.0", c.tag());
    assertEquals("sha256:75796f97f4b5b51e7f6bec3673ba442b85cb6486bf737a37ce51d90266b4e176", c.hash().orElseThrow());
  }

  @Test
  public void testWithHash1()
  {
    final var c =
      NPAWorkExecutorContainerImage.of("registry.example.com:5000/io7mcom/idstore:1.0.0@sha256:75796f97f4b5b51e7f6bec3673ba442b85cb6486bf737a37ce51d90266b4e176");

    assertEquals("registry.example.com:5000", c.registry());
    assertEquals("io7mcom/idstore", c.name());
    assertEquals("1.0.0", c.tag());
    assertEquals("sha256:75796f97f4b5b51e7f6bec3673ba442b85cb6486bf737a37ce51d90266b4e176", c.hash().orElseThrow());
  }

  @Test
  public void testWithoutHash0()
  {
    final var c =
      NPAWorkExecutorContainerImage.of("quay.io/io7mcom/idstore:1.0.0");

    assertEquals("quay.io", c.registry());
    assertEquals("io7mcom/idstore", c.name());
    assertEquals("1.0.0", c.tag());
    assertEquals(Optional.empty(), c.hash());
  }

  @Test
  public void testWithoutHash1()
  {
    final var c =
      NPAWorkExecutorContainerImage.of("registry.example.com:5000/io7mcom/idstore:1.0.0");

    assertEquals("registry.example.com:5000", c.registry());
    assertEquals("io7mcom/idstore", c.name());
    assertEquals("1.0.0", c.tag());
    assertEquals(Optional.empty(), c.hash());
  }
}
