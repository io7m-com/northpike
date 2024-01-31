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
import com.io7m.northpike.model.NPDocumentation;

import java.util.List;

/**
 * The roles.
 */

public enum NPSecRole
{
  /**
   * The all-powerful admin role. Use with extreme care.
   */

  @NPDocumentation("The all-powerful admin role. Use with extreme care.")
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

  @NPDocumentation("A role that allows logging in.")
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

  @NPDocumentation("A role for reading SCM providers.")
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

  @NPDocumentation("A role for writing SCM providers.")
  SCM_PROVIDERS_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("scm_providers.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading repositories.
   */

  @NPDocumentation("A role for reading repositories.")
  REPOSITORIES_READER {
    private static final MRoleName NAME =
      MRoleName.of("repositories.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for writing repositories.
   */

  @NPDocumentation("A role for writing repositories.")
  REPOSITORIES_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("repositories.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading assignments.
   */

  @NPDocumentation("A role for reading assignments.")
  ASSIGNMENTS_READER {
    private static final MRoleName NAME =
      MRoleName.of("assignments.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for executing assignments.
   */

  @NPDocumentation("A role for executing assignments.")
  ASSIGNMENTS_EXECUTOR {
    private static final MRoleName NAME =
      MRoleName.of("assignments.executor");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for writing assignments.
   */

  @NPDocumentation("A role for writing assignments.")
  ASSIGNMENTS_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("assignments.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for writing to assignment executions.
   */

  @NPDocumentation("A role for writing to assignment executions.")
  ASSIGNMENT_EXECUTIONS_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("assignment_executions.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading assignment executions.
   */

  @NPDocumentation("A role for reading assignment executions.")
  ASSIGNMENT_EXECUTIONS_READER {
    private static final MRoleName NAME =
      MRoleName.of("assignment_executions.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading tools.
   */

  @NPDocumentation("A role for reading tools.")
  TOOLS_READER {
    private static final MRoleName NAME =
      MRoleName.of("tools.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for writing tools.
   */

  @NPDocumentation("A role for writing tools.")
  TOOLS_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("tools.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading public keys.
   */

  @NPDocumentation("A role for reading public keys.")
  PUBLIC_KEYS_READER {
    private static final MRoleName NAME =
      MRoleName.of("public_keys.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for writing public keys.
   */

  @NPDocumentation("A role for writing public keys.")
  PUBLIC_KEYS_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("public_keys.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading plans.
   */

  @NPDocumentation("A role for reading plans.")
  PLANS_READER {
    private static final MRoleName NAME =
      MRoleName.of("plans.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for writing plans.
   */

  @NPDocumentation("A role for writing plans.")
  PLANS_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("plans.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading agents.
   */

  @NPDocumentation("A role for reading agents.")
  AGENTS_READER {
    private static final MRoleName NAME =
      MRoleName.of("agents.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for writing agents.
   */

  @NPDocumentation("A role for writing agents.")
  AGENTS_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("agents.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading agent labels.
   */

  @NPDocumentation("A role for reading agent labels.")
  AGENT_LABELS_READER {
    private static final MRoleName NAME =
      MRoleName.of("agent_labels.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for writing agent labels.
   */

  @NPDocumentation("A role for writing agent labels.")
  AGENT_LABELS_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("agent_labels.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading agent login challenges.
   */

  @NPDocumentation("A role for reading agent login challenges.")
  AGENT_LOGIN_CHALLENGE_READER {
    private static final MRoleName NAME =
      MRoleName.of("agent_login_challenge.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for writing agent login challenges.
   */

  @NPDocumentation("A role for writing agent login challenges.")
  AGENT_LOGIN_CHALLENGE_WRITER {
    private static final MRoleName NAME =
      MRoleName.of("agent_login_challenge.writer");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading the audit log.
   */

  @NPDocumentation("A role for reading the audit log.")
  AUDIT_LOG_READER {
    private static final MRoleName NAME =
      MRoleName.of("audit_log.reader");

    @Override
    public MRoleName role()
    {
      return NAME;
    }
  },

  /**
   * A role for reading users.
   */

  @NPDocumentation("A role for reading users.")
  USERS_READER {
    private static final MRoleName NAME =
      MRoleName.of("users.reader");

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
