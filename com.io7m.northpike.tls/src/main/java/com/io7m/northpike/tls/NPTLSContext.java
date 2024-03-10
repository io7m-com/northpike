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

import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.net.ssl.KeyManager;
import javax.net.ssl.KeyManagerFactory;
import javax.net.ssl.SSLContext;
import javax.net.ssl.TrustManager;
import javax.net.ssl.TrustManagerFactory;
import java.io.IOException;
import java.nio.file.Files;
import java.security.GeneralSecurityException;
import java.security.KeyStore;
import java.security.SecureRandom;
import java.util.Objects;
import java.util.Optional;

/**
 * Functions to create custom SSL contexts.
 */

public final class NPTLSContext
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPTLSContext.class);

  private final String user;
  private final Optional<KeyStoreConfigured> keyStoreConfigured;
  private final Optional<TrustStoreConfigured> trustStoreConfigured;
  private final SSLContext context;

  private NPTLSContext(
    final String inUser,
    final Optional<KeyStoreConfigured> inKeyStoreConfigured,
    final Optional<TrustStoreConfigured> inTrustStoreConfigured,
    final SSLContext inContext)
  {
    this.user =
      Objects.requireNonNull(inUser, "user");
    this.keyStoreConfigured =
      Objects.requireNonNull(inKeyStoreConfigured, "inKeyStoreConfigured");
    this.trustStoreConfigured =
      Objects.requireNonNull(inTrustStoreConfigured, "inTrustStoreConfigured");
    this.context =
      Objects.requireNonNull(inContext, "context");
  }

  private record KeyStoreConfigured(
    KeyStore store,
    NPTLSStoreConfiguration configuration)
  {

  }

  private record TrustStoreConfigured(
    KeyStore store,
    NPTLSStoreConfiguration configuration)
  {

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

  public static NPTLSContext create(
    final String user,
    final Optional<NPTLSStoreConfiguration> keyStoreConfiguration,
    final Optional<NPTLSStoreConfiguration> trustStoreConfiguration)
    throws IOException, GeneralSecurityException
  {
    Objects.requireNonNull(user, "user");
    Objects.requireNonNull(keyStoreConfiguration, "keyStoreConfiguration");
    Objects.requireNonNull(trustStoreConfiguration, "trustStoreConfiguration");

    if (keyStoreConfiguration.isPresent()) {
      final var c = keyStoreConfiguration.get();
      LOG.info(
        "KeyStore [{}] {} (Provider {}, Type {})",
        user,
        c.storePath(),
        c.storeProvider(),
        c.storeType()
      );
    }

    if (trustStoreConfiguration.isPresent()) {
      final var c = trustStoreConfiguration.get();
      LOG.info(
        "TrustStore [{}] {} (Provider {}, Type {})",
        user,
        c.storePath(),
        c.storeProvider(),
        c.storeType()
      );
    }

    final KeyManager[] keyManagers;
    final Optional<KeyStoreConfigured> keyStoreConfigured;
    if (keyStoreConfiguration.isPresent()) {
      final var c = keyStoreConfiguration.get();

      final var keyStore =
        KeyStore.getInstance(c.storeType(), c.storeProvider());
      final var keyStorePassChars =
        c.storePassword().toCharArray();

      try (var stream = Files.newInputStream(c.storePath())) {
        keyStore.load(stream, keyStorePassChars);
      }

      final var keyManagerFactory =
        createKeyManagerFactory(keyStore, keyStorePassChars);

      keyManagers = keyManagerFactory.getKeyManagers();
      keyStoreConfigured = Optional.of(new KeyStoreConfigured(keyStore, c));
    } else {
      keyManagers = null;
      keyStoreConfigured = Optional.empty();
    }

    final TrustManager[] trustManagers;
    final Optional<TrustStoreConfigured> trustStoreConfigured;
    if (trustStoreConfiguration.isPresent()) {
      final var c = trustStoreConfiguration.get();

      final var trustStore =
        KeyStore.getInstance(c.storeType(), c.storeProvider());
      final var trustStorePassChars =
        c.storePassword().toCharArray();

      try (var stream = Files.newInputStream(c.storePath())) {
        trustStore.load(stream, trustStorePassChars);
      }

      final var trustManagerFactory =
        createTrustManagerFactory(trustStore);

      trustManagers = trustManagerFactory.getTrustManagers();
      trustStoreConfigured =
        Optional.of(new TrustStoreConfigured(trustStore, c));
    } else {
      trustManagers = null;
      trustStoreConfigured = Optional.empty();
    }

    final var context =
      SSLContext.getInstance("TLSv1.3");

    context.init(
      keyManagers,
      trustManagers,
      SecureRandom.getInstanceStrong()
    );

    return new NPTLSContext(
      user,
      keyStoreConfigured,
      trustStoreConfigured,
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
    final KeyManager[] keyManagers;
    if (this.keyStoreConfigured.isPresent()) {
      final var configured = this.keyStoreConfigured.get();

      LOG.info(
        "KeyStore [{}] {} reloading",
        this.user,
        configured.configuration.storePath()
      );

      final var keyStorePassChars =
        configured.configuration.storePassword()
          .toCharArray();

      try (var stream =
             Files.newInputStream(configured.configuration.storePath())) {
        configured.store.load(stream, keyStorePassChars);
      }

      final var keyManagerFactory =
        createKeyManagerFactory(configured.store, keyStorePassChars);

      keyManagers = keyManagerFactory.getKeyManagers();
    } else {
      keyManagers = null;
    }

    final TrustManager[] trustManagers;
    if (this.trustStoreConfigured.isPresent()) {
      final var configured = this.trustStoreConfigured.get();

      LOG.info(
        "TrustStore [{}] {} reloading",
        this.user,
        configured.configuration.storePath()
      );

      final var trustStorePassChars =
        configured.configuration.storePassword().toCharArray();

      try (var stream =
             Files.newInputStream(configured.configuration.storePath())) {
        configured.store.load(stream, trustStorePassChars);
      }

      final var trustManagerFactory =
        createTrustManagerFactory(configured.store);

      trustManagers = trustManagerFactory.getTrustManagers();
    } else {
      trustManagers = null;
    }

    this.context.init(
      keyManagers,
      trustManagers,
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
