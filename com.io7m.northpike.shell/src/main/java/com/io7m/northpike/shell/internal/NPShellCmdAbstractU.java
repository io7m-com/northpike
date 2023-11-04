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

import com.io7m.northpike.shell.commons.NPShellCmdAbstract;
import com.io7m.northpike.user_client.api.NPUserClientType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.repetoir.core.RPServiceDirectoryType;

/**
 * An abstract command that gives access to a user client.
 */

public abstract class NPShellCmdAbstractU extends NPShellCmdAbstract
{
  protected NPShellCmdAbstractU(
    final RPServiceDirectoryType inServices,
    final QCommandMetadata inMetadata)
  {
    super(inServices, inMetadata);
  }

  protected final NPUserClientType client()
  {
    return this.services().requireService(NPUserClientType.class);
  }
}
