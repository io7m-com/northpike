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

import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.tests.arbitraries.NPArbAbstract;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;

import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public final class NPArbUMessage extends NPArbAbstract<NPUMessageType>
{
  public NPArbUMessage()
  {
    super(
      NPUMessageType.class,
      () -> Arbitraries.oneOf(arbitrariesForAllSubclasses())
    );
  }

  @SuppressWarnings("unchecked")
  private static Collection<Arbitrary<? extends NPUMessageType>> arbitrariesForAllSubclasses()
  {
    return (Collection<Arbitrary<? extends NPUMessageType>>) (Object) findAllMessageClasses()
      .stream()
      .map(Arbitraries::defaultFor)
      .map(a -> (Arbitrary<? extends NPUMessageType>) a)
      .toList();
  }

  private static Comparator<Class<?>> comparator()
  {
    return Comparator.comparing(Class::getCanonicalName);
  }

  private static List<Class<?>> findAllMessageClasses()
  {
    final var results = new HashSet<Class<?>>();
    permitted(NPUMessageType.class, results);
    return results.stream()
      .sorted(comparator())
      .toList();
  }

  private static void permitted(
    final Class<?> c,
    final Set<Class<?>> results)
  {
    if (c.isRecord()) {
      results.add(c);
    }

    final var p = permittedSubclasses(c);
    for (final var q : p) {
      permitted(q, results);
    }
  }

  private static Class<?>[] permittedSubclasses(
    final Class<?> c)
  {
    final var a = c.getPermittedSubclasses();
    if (a == null) {
      return new Class[0];
    }
    return a;
  }
}
