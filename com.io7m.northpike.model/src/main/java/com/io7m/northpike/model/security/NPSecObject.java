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

import com.io7m.medrina.api.MObject;
import com.io7m.medrina.api.MTypeName;

import java.util.Map;

/**
 * The objects.
 */

public enum NPSecObject
{
  /**
   * The server.
   */

  SERVER {
    private static final MObject SERVER_OBJECT =
      new MObject(MTypeName.of("server"), Map.of());

    @Override
    public MObject object()
    {
      return SERVER_OBJECT;
    }
  },

  /**
   * The agents.
   */

  AGENTS {
    private static final MObject AGENTS_OBJECT =
      new MObject(MTypeName.of("agents"), Map.of());

    @Override
    public MObject object()
    {
      return AGENTS_OBJECT;
    }
  },

  /**
   * The agent labels.
   */

  AGENT_LABELS {
    private static final MObject AGENT_LABELS_OBJECT =
      new MObject(MTypeName.of("agent_labels"), Map.of());

    @Override
    public MObject object()
    {
      return AGENT_LABELS_OBJECT;
    }
  },

  /**
   * The plans.
   */

  PLANS {
    private static final MObject PLANS_OBJECT =
      new MObject(MTypeName.of("plans"), Map.of());

    @Override
    public MObject object()
    {
      return PLANS_OBJECT;
    }
  },

  /**
   * The repositories.
   */

  REPOSITORIES {
    private static final MObject REPOSITORIES_OBJECT =
      new MObject(MTypeName.of("repositories"), Map.of());

    @Override
    public MObject object()
    {
      return REPOSITORIES_OBJECT;
    }
  },

  /**
   * The assignments.
   */

  ASSIGNMENTS {
    private static final MObject ASSIGNMENTS_OBJECT =
      new MObject(MTypeName.of("assignments"), Map.of());

    @Override
    public MObject object()
    {
      return ASSIGNMENTS_OBJECT;
    }
  },

  /**
   * The SCM providers.
   */

  SCM_PROVIDERS {
    private static final MObject SCM_PROVIDERS_OBJECT =
      new MObject(MTypeName.of("scm_providers"), Map.of());

    @Override
    public MObject object()
    {
      return SCM_PROVIDERS_OBJECT;
    }
  },

  /**
   * The tools.
   */

  TOOLS {
    private static final MObject TOOLS_OBJECT =
      new MObject(MTypeName.of("tools"), Map.of());

    @Override
    public MObject object()
    {
      return TOOLS_OBJECT;
    }
  },

  /**
   * The public keys.
   */

  PUBLIC_KEYS {
    private static final MObject PUBLIC_KEYS_OBJECT =
      new MObject(MTypeName.of("public_keys"), Map.of());

    @Override
    public MObject object()
    {
      return PUBLIC_KEYS_OBJECT;
    }
  },

  /**
   * The users.
   */

  USERS {
    private static final MObject USERS_OBJECT =
      new MObject(MTypeName.of("users"), Map.of());

    @Override
    public MObject object()
    {
      return USERS_OBJECT;
    }
  };

  /**
   * @return The medrina object
   */

  public abstract MObject object();
}
