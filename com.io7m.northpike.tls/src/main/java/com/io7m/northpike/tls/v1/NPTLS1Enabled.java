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

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.blackthorne.core.Blackthorne;
import com.io7m.northpike.model.tls.NPTLSEnabled;
import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;

import java.util.Map;

import static com.io7m.northpike.tls.v1.NPTLS1.element;

/**
 * Parser for the TLS Enabled element.
 */

public final class NPTLS1Enabled
  implements BTElementHandlerType<Object, NPTLSEnabled>
{
  private TrustStore trustStore;
  private KeyStore keyStore;

  /**
   * Parser for the TLS Enabled element.
   *
   * @param context The parse context
   */

  public NPTLS1Enabled(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ?>> onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      Map.entry(
        element("KeyStore"),
        Blackthorne.mapConstructor(NPTLS1Store::new, KeyStore::new)
      ),
      Map.entry(
        element("TrustStore"),
        Blackthorne.mapConstructor(NPTLS1Store::new, TrustStore::new)
      )
    );
  }

  private record KeyStore(NPTLSStoreConfiguration configuration)
  {

  }

  private record TrustStore(NPTLSStoreConfiguration configuration)
  {

  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final Object result)
    throws Exception
  {
    if (result instanceof final KeyStore ks) {
      this.keyStore = ks;
      return;
    }
    if (result instanceof final TrustStore ts) {
      this.trustStore = ts;
      return;
    }
    throw new IllegalStateException("Unrecognized result: " + result);
  }

  @Override
  public NPTLSEnabled onElementFinished(
    final BTElementParsingContextType context)
    throws Exception
  {
    return new NPTLSEnabled(
      this.keyStore.configuration,
      this.trustStore.configuration
    );
  }
}
