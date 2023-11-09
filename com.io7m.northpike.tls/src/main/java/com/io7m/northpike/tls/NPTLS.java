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


package com.io7m.northpike.tls;

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.northpike.model.tls.NPTLSConfigurationType;
import com.io7m.northpike.tls.v1.NPTLS1;

import java.util.Map;

/**
 * Access to TLS configuration element parsers.
 */

public final class NPTLS
{
  private NPTLS()
  {

  }

  /**
   * @return A parser for TLS configuration elements.
   */

  public static BTElementHandlerConstructorType<?, NPTLSConfigurationType> configuration()
  {
    return NPTLS1.configuration();
  }

  /**
   * @return A parser for TLS configuration elements.
   */

  public static Map<
    BTQualifiedName,
    BTElementHandlerConstructorType<?, ? extends NPTLSConfigurationType>>
  configurationElements()
  {
    return NPTLS1.configurationElements();
  }
}
