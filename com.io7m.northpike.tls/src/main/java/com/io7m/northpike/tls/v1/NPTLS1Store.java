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


package com.io7m.northpike.tls.v1;

import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import org.xml.sax.Attributes;

import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * Parser for TLS store elements.
 */

public final class NPTLS1Store
  implements BTElementHandlerType<Object, NPTLSStoreConfiguration>
{
  private String type;
  private String provider;
  private String password;
  private Path file;

  /**
   * Parser for TLS store elements.
   *
   * @param context The parser context
   */

  public NPTLS1Store(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.type =
      attributes.getValue("Type");
    this.provider =
      attributes.getValue("Provider");
    this.password =
      attributes.getValue("Password");
    this.file =
      Paths.get(attributes.getValue("File"));
  }

  @Override
  public NPTLSStoreConfiguration onElementFinished(
    final BTElementParsingContextType context)
    throws Exception
  {
    return new NPTLSStoreConfiguration(
      this.type,
      this.provider,
      this.password,
      this.file
    );
  }
}
