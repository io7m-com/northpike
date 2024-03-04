/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.toolexec.js;

import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.toolexec.api.NPTEvaluableType;
import com.io7m.northpike.toolexec.api.NPTEvaluationLanguageProviderType;
import com.io7m.northpike.toolexec.js.internal.NPTJs;

import java.util.Map;

/**
 * A toolexec Javascript provider.
 */

public final class NPTJSLanguageProvider
  implements NPTEvaluationLanguageProviderType
{
  private static final NPFormatName FORMAT_NAME =
    NPFormatName.of("com.io7m.northpike.toolexec.js");

  /**
   * A toolexec Javascript provider.
   */

  public NPTJSLanguageProvider()
  {

  }

  @Override
  public NPFormatName languageSupported()
  {
    return FORMAT_NAME;
  }

  @Override
  public NPTEvaluableType create(
    final Map<String, String> initialEnvironment,
    final String program)
  {
    return new NPTJs(initialEnvironment, program);
  }
}
