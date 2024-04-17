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


package com.io7m.northpike.tests.arbitraries;

import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.Combinators;

import java.net.Inet4Address;
import java.net.Inet6Address;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.UnknownHostException;
import java.util.Locale;

public final class NPArbInetSocketAddress extends NPArbAbstract<InetSocketAddress>
{
  public NPArbInetSocketAddress()
  {
    super(
      InetSocketAddress.class,
      () -> Combinators.combine(
        Arbitraries.oneOf(ipv4(), ipv6()),
        Arbitraries.integers().between(1, 65535)
      ).as(InetSocketAddress::new)
    );
  }

  private static Arbitrary<InetAddress> ipv4()
  {
    return Arbitraries.bytes()
      .array(byte[].class)
      .ofSize(4)
      .map(x -> {
        try {
          return Inet4Address.getByAddress(x);
        } catch (final UnknownHostException e) {
          throw new RuntimeException(e);
        }
      });
  }

  private static Arbitrary<InetAddress> ipv6()
  {
    return Arbitraries.bytes()
      .array(byte[].class)
      .ofSize(16)
      .map(x -> {
        try {
          return Inet6Address.getByAddress(x);
        } catch (final UnknownHostException e) {
          throw new RuntimeException(e);
        }
      });
  }
}
