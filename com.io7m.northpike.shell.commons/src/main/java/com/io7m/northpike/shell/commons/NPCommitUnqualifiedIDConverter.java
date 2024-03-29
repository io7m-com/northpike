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


package com.io7m.northpike.shell.commons;

import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.quarrel.core.QValueConverterType;

/**
 * @see NPCommitUnqualifiedID
 */

public final class NPCommitUnqualifiedIDConverter
  implements QValueConverterType<NPCommitUnqualifiedID>
{
  static final String COMMIT_SYNTAX =
    "[a-f0-9]{1,8192}";

  /**
   * @see NPCommitUnqualifiedID
   */

  public NPCommitUnqualifiedIDConverter()
  {

  }

  @Override
  public NPCommitUnqualifiedID convertFromString(
    final String text)
  {
    return new NPCommitUnqualifiedID(text);
  }

  @Override
  public String convertToString(
    final NPCommitUnqualifiedID value)
  {
    return value.toString();
  }

  @Override
  public NPCommitUnqualifiedID exampleValue()
  {
    return new NPCommitUnqualifiedID("fc146e92ccddd34d7160dad7e14a89b93e7a6241");
  }

  @Override
  public String syntax()
  {
    return COMMIT_SYNTAX;
  }

  @Override
  public Class<NPCommitUnqualifiedID> convertedClass()
  {
    return NPCommitUnqualifiedID.class;
  }
}
