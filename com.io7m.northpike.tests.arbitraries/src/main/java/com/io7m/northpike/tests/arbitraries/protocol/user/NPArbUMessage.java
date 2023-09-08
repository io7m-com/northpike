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


package com.io7m.northpike.tests.arbitraries.protocol.user;

import com.io7m.northpike.protocol.user.NPUCommandDisconnect;
import com.io7m.northpike.protocol.user.NPUCommandLogin;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryGet;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPut;
import com.io7m.northpike.protocol.user.NPUCommandRolesAssign;
import com.io7m.northpike.protocol.user.NPUCommandRolesGet;
import com.io7m.northpike.protocol.user.NPUCommandRolesRevoke;
import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.protocol.user.NPUResponseError;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.protocol.user.NPUResponseRepositoryGet;
import com.io7m.northpike.protocol.user.NPUResponseRolesGet;
import com.io7m.northpike.tests.arbitraries.NPArbAbstract;
import net.jqwik.api.Arbitraries;

import java.util.stream.Collectors;
import java.util.stream.Stream;

public final class NPArbUMessage extends NPArbAbstract<NPUMessageType>
{
  public NPArbUMessage()
  {
    super(
      NPUMessageType.class,
      () -> {
        return Arbitraries.oneOf(
          Stream.of(
              NPUCommandDisconnect.class,
              NPUCommandLogin.class,
              NPUCommandRepositoryGet.class,
              NPUCommandRepositoryPut.class,
              NPUCommandRolesAssign.class,
              NPUCommandRolesGet.class,
              NPUCommandRolesRevoke.class,
              NPUResponseError.class,
              NPUResponseOK.class,
              NPUResponseRepositoryGet.class,
              NPUResponseRolesGet.class
            ).map(Arbitraries::defaultFor)
            .collect(Collectors.toUnmodifiableList())
        );
      }
    );
  }
}
