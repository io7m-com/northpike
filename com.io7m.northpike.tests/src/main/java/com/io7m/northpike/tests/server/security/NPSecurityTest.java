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


package com.io7m.northpike.tests.server.security;

import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.server.internal.security.NPSecurityException;
import com.io7m.northpike.server.internal.security.NPSecurityPolicy;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.Provide;
import net.jqwik.api.arbitraries.SetArbitrary;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;
import java.util.UUID;
import java.util.stream.Collectors;

import static com.io7m.northpike.model.security.NPSecAction.READ;
import static com.io7m.northpike.model.security.NPSecAction.WRITE;
import static com.io7m.northpike.model.security.NPSecObject.SCM_PROVIDERS;
import static com.io7m.northpike.model.security.NPSecObject.SERVER;
import static com.io7m.northpike.model.security.NPSecRole.ADMINISTRATOR;
import static com.io7m.northpike.model.security.NPSecRole.LOGIN;
import static com.io7m.northpike.model.security.NPSecRole.SCM_PROVIDERS_READER;
import static com.io7m.northpike.model.security.NPSecRole.SCM_PROVIDERS_WRITER;
import static org.junit.jupiter.api.Assertions.assertThrows;

public final class NPSecurityTest
{
  @Provide
  public static SetArbitrary<NPSecRole> roles()
  {
    return Arbitraries.defaultFor(NPSecRole.class)
      .set()
      .ofMinSize(0)
      .ofMaxSize(8);
  }

  /**
   * The default policy denies everything.
   *
   * @param roles  The roles
   * @param object The object
   * @param action The action
   */

  @Property
  public void testDefaultDeny(
    final @ForAll("roles") Set<NPSecRole> roles,
    final @ForAll NPSecObject object,
    final @ForAll NPSecAction action)
  {
    NPSecurity.setPolicy(new MPolicy(List.of()));

    assertThrows(NPSecurityException.class, () -> {
      NPSecurity.check(
        UUID.randomUUID(),
        new MSubject(
          roles.stream()
            .map(NPSecRole::role)
            .collect(Collectors.toUnmodifiableSet())
        ),
        object.object(),
        action.action()
      );
    });
  }

  /**
   * Being an administrator doesn't imply a login capability.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAdminNotLogin()
    throws Exception
  {
    NPSecurity.setPolicy(NPSecurityPolicy.open());
    checkNotAllowed(ADMINISTRATOR, SERVER, NPSecAction.LOGIN);
  }

  /**
   * The security policy allows this action.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAllowAction0()
    throws Exception
  {
    NPSecurity.setPolicy(NPSecurityPolicy.open());
    checkAllowed(SCM_PROVIDERS_READER, SCM_PROVIDERS, READ);
  }

  /**
   * The security policy allows this action.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAllowAction1()
    throws Exception
  {
    NPSecurity.setPolicy(NPSecurityPolicy.open());
    checkAllowed(SCM_PROVIDERS_WRITER, SCM_PROVIDERS, WRITE);
  }

  /**
   * The security policy allows this action.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAllowAction2()
    throws Exception
  {
    NPSecurity.setPolicy(NPSecurityPolicy.open());
    checkAllowed(LOGIN, SERVER, NPSecAction.LOGIN);
  }

  private static void checkAllowed(
    final NPSecRole role,
    final NPSecObject object,
    final NPSecAction action)
    throws NPSecurityException
  {
    NPSecurity.check(
      UUID.randomUUID(),
      new MSubject(Set.of(role.role())),
      object.object(),
      action.action()
    );
  }

  private static void checkNotAllowed(
    final NPSecRole role,
    final NPSecObject object,
    final NPSecAction action)
  {
    assertThrows(NPSecurityException.class, () -> {
      NPSecurity.check(
        UUID.randomUUID(),
        new MSubject(Set.of(role.role())),
        object.object(),
        action.action()
      );
    });
  }
}
