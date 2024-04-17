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


package com.io7m.northpike.protocol.user.cb.internal;

import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1IPAddress;

import java.net.Inet4Address;
import java.net.Inet6Address;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;

import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned16;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned8;

/**
 * A validator.
 */

public enum NPUVIPAddress
  implements NPProtocolMessageValidatorType<InetAddress, NPU1IPAddress>
{
  /**
   * A validator.
   */

  IP_ADDRESS;

  @Override
  public NPU1IPAddress convertToWire(
    final InetAddress message)
  {
    return switch (message) {
      case final Inet4Address i4 -> {
        final var a = i4.getAddress();

        yield new NPU1IPAddress.IPv4(
          unsigned8((int) a[0] & 0xff),
          unsigned8((int) a[1] & 0xff),
          unsigned8((int) a[2] & 0xff),
          unsigned8((int) a[3] & 0xff)
        );
      }

      case final Inet6Address i6 -> {
        final var a =
          ByteBuffer.wrap(i6.getAddress())
            .order(ByteOrder.BIG_ENDIAN);

        yield new NPU1IPAddress.IPv6(
          unsigned16((int) a.getChar(0)),
          unsigned16((int) a.getChar(2)),
          unsigned16((int) a.getChar(4)),
          unsigned16((int) a.getChar(6)),
          unsigned16((int) a.getChar(8)),
          unsigned16((int) a.getChar(10)),
          unsigned16((int) a.getChar(12)),
          unsigned16((int) a.getChar(14))
        );
      }

      default -> {
        throw new IllegalStateException("Unexpected value: " + message);
      }
    };
  }

  @Override
  public InetAddress convertFromWire(
    final NPU1IPAddress message)
  {
    try {
      return switch (message) {
        case final NPU1IPAddress.IPv4 iPv4 -> {
          final var addr = new byte[4];
          addr[0] = (byte) (iPv4.fieldS0().value() & 0xff);
          addr[1] = (byte) (iPv4.fieldS1().value() & 0xff);
          addr[2] = (byte) (iPv4.fieldS2().value() & 0xff);
          addr[3] = (byte) (iPv4.fieldS3().value() & 0xff);
          yield Inet4Address.getByAddress(addr);
        }
        case final NPU1IPAddress.IPv6 iPv6 -> {
          final var buffer = new byte[16];

          final var addr =
            ByteBuffer.wrap(buffer)
              .order(ByteOrder.BIG_ENDIAN);

          addr.putChar((char) iPv6.fieldS0().value());
          addr.putChar((char) iPv6.fieldS1().value());
          addr.putChar((char) iPv6.fieldS2().value());
          addr.putChar((char) iPv6.fieldS3().value());
          addr.putChar((char) iPv6.fieldS4().value());
          addr.putChar((char) iPv6.fieldS5().value());
          addr.putChar((char) iPv6.fieldS6().value());
          addr.putChar((char) iPv6.fieldS7().value());
          yield Inet6Address.getByAddress(buffer);
        }
      };
    } catch (final UnknownHostException e) {
      throw new IllegalArgumentException("Failed to parse IP address.", e);
    }
  }
}
