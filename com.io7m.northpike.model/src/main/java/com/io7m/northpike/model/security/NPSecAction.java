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

import com.io7m.medrina.api.MActionName;

/**
 * The actions.
 */

public enum NPSecAction
{
  /**
   * A read operation.
   */

  READ {
    private static final MActionName READ_OBJECT =
      MActionName.of("read");

    @Override
    public MActionName action()
    {
      return READ_OBJECT;
    }
  },

  /**
   * An enumerate operation.
   */

  ENUMERATE {
    private static final MActionName ENUMERATE_OBJECT =
      MActionName.of("enumerate");

    @Override
    public MActionName action()
    {
      return ENUMERATE_OBJECT;
    }
  },

  /**
   * A write operation.
   */

  WRITE {
    private static final MActionName WRITE_OBJECT =
      MActionName.of("write");

    @Override
    public MActionName action()
    {
      return WRITE_OBJECT;
    }
  },

  /**
   * An execute operation.
   */

  EXECUTE {
    private static final MActionName EXECUTE_OBJECT =
      MActionName.of("execute");

    @Override
    public MActionName action()
    {
      return EXECUTE_OBJECT;
    }
  },

  /**
   * A delete operation.
   */

  DELETE {
    private static final MActionName DELETE_OBJECT =
      MActionName.of("delete");

    @Override
    public MActionName action()
    {
      return DELETE_OBJECT;
    }
  },

  /**
   * A login operation.
   */

  LOGIN {
    private static final MActionName LOGIN_OBJECT =
      MActionName.of("login");

    @Override
    public MActionName action()
    {
      return LOGIN_OBJECT;
    }
  },

  /**
   * A key assignment operation.
   */

  KEY_ASSIGN {
    private static final MActionName KEY_ASSIGN_OBJECT =
      MActionName.of("key_assign");

    @Override
    public MActionName action()
    {
      return KEY_ASSIGN_OBJECT;
    }
  },

  /**
   * A key unassignment operation.
   */

  KEY_UNASSIGN {
    private static final MActionName KEY_UNASSIGN_OBJECT =
      MActionName.of("key_unassign");

    @Override
    public MActionName action()
    {
      return KEY_UNASSIGN_OBJECT;
    }
  };

  /**
   * @return The medrina object
   */

  public abstract MActionName action();
}
