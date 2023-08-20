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


package com.io7m.northpike.server.internal.tls;

import com.io7m.northpike.tls.NPTLSStoreConfiguration;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.net.ssl.KeyManagerFactory;
import javax.net.ssl.SSLContext;
import javax.net.ssl.TrustManagerFactory;
import java.io.IOException;
import java.nio.file.Files;
import java.security.GeneralSecurityException;
import java.security.KeyStore;
import java.security.SecureRandom;
import java.util.Objects;

/**
 * Functions to create custom SSL contexts.
 */

public final class NPTLSContext
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPTLSContext.class);

  private final String user;
  private final NPTLSStoreConfiguration keyStoreConfiguration;
  private final KeyStore keyStore;
  private final NPTLSStoreConfiguration trustStoreConfiguration;
  private final KeyStore trustStore;
  private final SSLContext context;

  private NPTLSContext(
    final String inUser,
    final NPTLSStoreConfiguration inKeyStoreConfiguration,
    final KeyStore inKeyStore,
    final NPTLSStoreConfiguration inTrustStoreConfiguration,
    final KeyStore inTrustStore,
    final SSLContext inContext)
  {
    this.user =
      Objects.requireNonNull(inUser, "user");
    this.keyStoreConfiguration =
      Objects.requireNonNull(inKeyStoreConfiguration, "keyStoreConfiguration");
    this.keyStore =
      Objects.requireNonNull(inKeyStore, "keyStore");
    this.trustStoreConfiguration =
      Objects.requireNonNull(
        inTrustStoreConfiguration,
        "trustStoreConfiguration");
    this.trustStore =
      Objects.requireNonNull(inTrustStore, "trustStore");
    this.context =
      Objects.requireNonNull(inContext, "context");
  }

  /**
   * Create a new SSL context using the given keystore and truststore.
   *
   * @param user                    The part of the application creating the context
   * @param keyStoreConfiguration   The key store
   * @param trustStoreConfiguration The trust store
   *
   * @return A new SSL context
   *
   * @throws IOException              On I/O errors
   * @throws GeneralSecurityException On security errors
   */

  static NPTLSContext create(
    final String user,
    final NPTLSStoreConfiguration keyStoreConfiguration,
    final NPTLSStoreConfiguration trustStoreConfiguration)
    throws IOException, GeneralSecurityException
  {
    LOG.info(
      "KeyStore [{}] {} (Provider {}, Type {})",
      user,
      keyStoreConfiguration.storePath(),
      keyStoreConfiguration.storeProvider(),
      keyStoreConfiguration.storeType()
    );

    LOG.info(
      "TrustStore [{}] {} (Provider {}, Type {})",
      user,
      trustStoreConfiguration.storePath(),
      trustStoreConfiguration.storeProvider(),
      trustStoreConfiguration.storeType()
    );

    final var keyStore =
      KeyStore.getInstance(
        keyStoreConfiguration.storeType(),
        keyStoreConfiguration.storeProvider()
      );

    final var keyStorePassChars =
      keyStoreConfiguration.storePassword()
        .toCharArray();

    try (var stream =
           Files.newInputStream(keyStoreConfiguration.storePath())) {
      keyStore.load(stream, keyStorePassChars);
    }

    final var trustStore =
      KeyStore.getInstance(
        trustStoreConfiguration.storeType(),
        trustStoreConfiguration.storeProvider()
      );

    final var trustStorePassChars =
      trustStoreConfiguration.storePassword().toCharArray();

    try (var stream = Files.newInputStream(trustStoreConfiguration.storePath())) {
      trustStore.load(stream, trustStorePassChars);
    }

    final var keyManagerFactory =
      createKeyManagerFactory(keyStore, keyStorePassChars);
    final var trustManagerFactory =
      createTrustManagerFactory(trustStore);

    final var context =
      SSLContext.getInstance("TLSv1.3");

    context.init(
      keyManagerFactory.getKeyManagers(),
      trustManagerFactory.getTrustManagers(),
      SecureRandom.getInstanceStrong()
    );

    return new NPTLSContext(
      user,
      keyStoreConfiguration,
      keyStore,
      trustStoreConfiguration,
      trustStore,
      context
    );
  }

  private static TrustManagerFactory createTrustManagerFactory(
    final KeyStore trustStore)
    throws GeneralSecurityException
  {
    final var trustManagerFactory =
      TrustManagerFactory.getInstance(TrustManagerFactory.getDefaultAlgorithm());

    trustManagerFactory.init(trustStore);
    return trustManagerFactory;
  }

  private static KeyManagerFactory createKeyManagerFactory(
    final KeyStore keyStore,
    final char[] keyStorePassChars)
    throws GeneralSecurityException
  {
    final var keyManagerFactory =
      KeyManagerFactory.getInstance(KeyManagerFactory.getDefaultAlgorithm());

    keyManagerFactory.init(keyStore, keyStorePassChars);
    return keyManagerFactory;
  }

  /**
   * Reload the key stores and associated SSL context.
   *
   * @throws IOException              On I/O errors
   * @throws GeneralSecurityException On security errors
   */

  public void reload()
    throws IOException, GeneralSecurityException
  {
    LOG.info(
      "KeyStore [{}] {} reloading",
      this.user,
      this.keyStoreConfiguration.storePath()
    );

    final var keyStorePassChars =
      this.keyStoreConfiguration.storePassword()
        .toCharArray();

    try (var stream =
           Files.newInputStream(this.keyStoreConfiguration.storePath())) {
      this.keyStore.load(stream, keyStorePassChars);
    }

    LOG.info(
      "TrustStore [{}] {} reloading",
      this.user,
      this.keyStoreConfiguration.storePath()
    );

    final var trustStorePassChars =
      this.trustStoreConfiguration.storePassword().toCharArray();

    try (var stream =
           Files.newInputStream(this.trustStoreConfiguration.storePath())) {
      this.trustStore.load(stream, trustStorePassChars);
    }

    final var keyManagerFactory =
      createKeyManagerFactory(this.keyStore, keyStorePassChars);
    final var trustManagerFactory =
      createTrustManagerFactory(this.trustStore);

    this.context.init(
      keyManagerFactory.getKeyManagers(),
      trustManagerFactory.getTrustManagers(),
      SecureRandom.getInstanceStrong()
    );
  }

  /**
   * @return The SSL context
   */

  public SSLContext context()
  {
    return this.context;
  }
}
