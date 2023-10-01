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


package com.io7m.northpike.shell.internal;


import com.io7m.medrina.api.MRoleName;
import com.io7m.northpike.model.security.NPRoleSet;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.quarrel.core.QValueConverterType;

import java.util.Arrays;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @see NPRoleSet
 */

public final class NPRoleSetConverter
  implements QValueConverterType<NPRoleSet>
{
  /**
   * @see NPRoleSet
   */

  public NPRoleSetConverter()
  {

  }

  @Override
  public NPRoleSet convertFromString(
    final String text)
  {
    return new NPRoleSet(
      Arrays.stream(text.split(","))
        .map(MRoleName::of)
        .collect(Collectors.toUnmodifiableSet())
    );
  }

  @Override
  public String convertToString(
    final NPRoleSet value)
  {
    return value.toString();
  }

  @Override
  public NPRoleSet exampleValue()
  {
    return new NPRoleSet(
      Set.of(
        NPSecRole.AGENTS_READER.role(),
        NPSecRole.AGENT_LABELS_READER.role(),
        NPSecRole.REPOSITORIES_READER.role()
      )
    );
  }

  @Override
  public String syntax()
  {
    return "<role-name> [',' <role-name>]";
  }

  @Override
  public Class<NPRoleSet> convertedClass()
  {
    return NPRoleSet.class;
  }
}
