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


package com.io7m.northpike.model.security;

import com.io7m.medrina.api.MRoleName;

import java.util.List;

/**
 * The roles.
 */

public enum NPSecRole
{
  /**
   * The all-powerful admin role. Use with extreme care.
   */

  ADMINISTRATOR {
    private static final MRoleName NAME =
      MRoleName.of("administrator");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role that allows logging in.
   */

  LOGIN {
    private static final MRoleName NAME =
      MRoleName.of("login");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading SCM providers.
   */

  SCM_PROVIDERS_READER {
    private static final MRoleName NAME =
      MRoleName.of("scm_providers.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for writing SCM providers.
   */

  SCM_PROVIDERS_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("scm_providers.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  };

  private static final List<NPSecRole> ROLES_ALL =
    List.of(values());

  /**
   * @return A read-only list of all the roles
   */

  public static List<NPSecRole> allRoles()
  {
    return ROLES_ALL;
  }

  /**
   * @return The medrina role
   */

  public abstract MRoleName role();
}
