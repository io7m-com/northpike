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


package com.io7m.northpike.model.agents;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPSignedData;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.math.BigInteger;
import java.security.GeneralSecurityException;
import java.security.KeyFactory;
import java.security.KeyPairGenerator;
import java.security.NoSuchAlgorithmException;
import java.security.Signature;
import java.security.interfaces.EdECPrivateKey;
import java.security.interfaces.EdECPublicKey;
import java.security.spec.EdECPoint;
import java.security.spec.EdECPublicKeySpec;
import java.security.spec.InvalidKeySpecException;
import java.security.spec.NamedParameterSpec;
import java.security.spec.PKCS8EncodedKeySpec;
import java.util.HexFormat;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Properties;

import static com.io7m.northpike.model.agents.NPAgentKeyPairEd448Type.ALGORITHM_NAME;
import static com.io7m.northpike.strings.NPStringConstants.EXPECTED;
import static com.io7m.northpike.strings.NPStringConstants.RECEIVED;

/**
 * A key pair factory for Ed448 keys.
 *
 * @see "https://en.wikipedia.org/wiki/Curve448"
 */

public final class NPAgentKeyPairFactoryEd448
  implements NPAgentKeyPairFactoryEd448Type
{
  private static final HexFormat HEX =
    HexFormat.of();
  private static final String PROP_ALGORITHM =
    "com.northpike.agent.keypair.algorithm";
  private static final String PROP_PRIVATE =
    "com.northpike.agent.keypair.private";
  private static final String PROP_PUBLIC =
    "com.northpike.agent.keypair.public";
  private static final String ED_448 =
    "Ed448";

  private final KeyPairGenerator generator;
  private final KeyFactory factory;
  private final NPStrings strings;

  /**
   * A key pair factory for Ed448 keys.
   */

  public NPAgentKeyPairFactoryEd448()
  {
    this(Locale.getDefault());
  }

  /**
   * A key pair factory for Ed448 keys.
   *
   * @param locale The locale
   */

  public NPAgentKeyPairFactoryEd448(
    final Locale locale)
  {
    this(NPStrings.create(locale));
  }

  /**
   * A key pair factory for Ed448 keys.
   *
   * @param inStrings The string resources
   */

  public NPAgentKeyPairFactoryEd448(
    final NPStrings inStrings)
  {
    try {
      this.strings =
        Objects.requireNonNull(inStrings, "strings");
      this.generator =
        KeyPairGenerator.getInstance("Ed448");
      this.factory =
        KeyFactory.getInstance("Ed448");
    } catch (final NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }

  @Override
  public NPAgentKeyPairEd448Type generateKeyPair()
  {
    final var keyPair =
      this.generator.generateKeyPair();

    final var keyPublic =
      (EdECPublicKey) keyPair.getPublic();
    final var keyPrivate =
      (EdECPrivateKey) keyPair.getPrivate();
    final var npKeyPublic =
      new NPAgentKeyPublicEd448(keyPublic);
    final var npKeyPrivate =
      new NPAgentKeyPrivateEd448(keyPrivate);

    return new NPAgentKeyPairEd448(npKeyPrivate, npKeyPublic);
  }

  @Override
  public NPAgentKeyPairEd448Type parseFromProperties(
    final Properties properties)
    throws NPException
  {
    Objects.requireNonNull(properties, "properties");

    final var algorithm =
      properties.getProperty(PROP_ALGORITHM);

    if (!Objects.equals(algorithm, ED_448)) {
      throw this.errorWrongAlgorithm(algorithm);
    }

    try {
      final var privateKeySpec =
        new PKCS8EncodedKeySpec(
          HEX.parseHex(properties.getProperty(PROP_PRIVATE)),
          ED_448
        );

      final var publicKeyText =
        properties.getProperty(PROP_PUBLIC);
      final EdECPublicKey publicKey =
        this.decodePublicKeyText(publicKeyText);

      final var privateKey =
        (EdECPrivateKey) this.factory.generatePrivate(privateKeySpec);

      return new NPAgentKeyPairEd448(
        new NPAgentKeyPrivateEd448(privateKey),
        new NPAgentKeyPublicEd448(publicKey)
      );
    } catch (final InvalidKeySpecException e) {
      throw new NPException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorParse(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  @Override
  public NPAgentKeyPublicEd448Type parsePublicKeyFromText(
    final String publicKey)
    throws NPException
  {
    return new NPAgentKeyPublicEd448(this.decodePublicKeyText(publicKey));
  }

  private EdECPublicKey decodePublicKeyText(
    final String publicKeyText)
    throws NPException
  {
    return this.decodePublicKeyBytes(HEX.parseHex(publicKeyText));
  }

  private EdECPublicKey decodePublicKeyBytes(
    final byte[] publicKeyEncoded)
    throws NPException
  {
    try {
      final var publicKeyStream =
        new ByteArrayInputStream(publicKeyEncoded);
      final var publicKeyOdd =
        publicKeyStream.read();
      final var publicKeyPointData =
        publicKeyStream.readAllBytes();
      final var publicKeyPoint =
        new BigInteger(publicKeyPointData);
      final var publicKeySpec =
        new EdECPublicKeySpec(
          new NamedParameterSpec(ED_448),
          new EdECPoint(publicKeyOdd == 1, publicKeyPoint)
        );

      return (EdECPublicKey) this.factory.generatePublic(publicKeySpec);
    } catch (final InvalidKeySpecException e) {
      throw new NPException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorParse(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  @Override
  public NPAgentKeyPublicEd448Type parsePublicKeyFromBytes(
    final byte[] publicKey)
    throws NPException
  {
    return new NPAgentKeyPublicEd448(this.decodePublicKeyBytes(publicKey));
  }

  @Override
  public NPAgentKeyPairType parseFromText(
    final String publicKey,
    final String privateKey)
    throws NPException
  {
    final var properties = new Properties();
    properties.setProperty(PROP_ALGORITHM, ALGORITHM_NAME);
    properties.setProperty(PROP_PUBLIC, publicKey);
    properties.setProperty(PROP_PRIVATE, privateKey);
    return this.parseFromProperties(properties);
  }

  private NPException errorWrongAlgorithm(
    final String algorithm)
  {
    return new NPException(
      this.strings.format(NPStringConstants.ERROR_WRONG_ALGORITHM),
      NPStandardErrorCodes.errorWrongAlgorithm(),
      Map.ofEntries(
        Map.entry(this.strings.format(EXPECTED), ED_448),
        Map.entry(this.strings.format(RECEIVED), algorithm)
      ),
      Optional.empty()
    );
  }

  private static final class NPAgentKeyPairEd448
    implements NPAgentKeyPairEd448Type
  {
    private final NPAgentKeyPrivateEd448 keyPrivate;
    private final NPAgentKeyPublicEd448 keyPublic;

    @Override
    public boolean equals(
      final Object o)
    {
      if (this == o) {
        return true;
      }
      if (o == null || !this.getClass().equals(o.getClass())) {
        return false;
      }
      final NPAgentKeyPairEd448 that = (NPAgentKeyPairEd448) o;
      return Objects.equals(this.keyPrivate, that.keyPrivate)
             && Objects.equals(this.keyPublic, that.keyPublic);
    }

    @Override
    public String toString()
    {
      return "[NPAgentKeyPairEd448 %s]".formatted(this.id());
    }

    @Override
    public int hashCode()
    {
      return Objects.hash(this.keyPrivate, this.keyPublic);
    }

    NPAgentKeyPairEd448(
      final NPAgentKeyPrivateEd448 inKeyPrivate,
      final NPAgentKeyPublicEd448 inKeyPublic)
    {
      this.keyPrivate =
        Objects.requireNonNull(inKeyPrivate, "inKeyPrivate");
      this.keyPublic =
        Objects.requireNonNull(inKeyPublic, "inKeyPublic");
    }

    @Override
    public NPAgentKeyPublicEd448Type publicKey()
    {
      return this.keyPublic;
    }

    @Override
    public NPAgentKeyPrivateEd448Type privateKey()
    {
      return this.keyPrivate;
    }

    @Override
    public Properties toProperties()
    {
      final var properties = new Properties();
      properties.setProperty(
        PROP_ALGORITHM,
        ED_448
      );
      properties.setProperty(
        PROP_PRIVATE,
        HEX.formatHex(this.keyPrivate.keyPrivate.getEncoded())
      );
      properties.setProperty(
        PROP_PUBLIC,
        HEX.formatHex(this.keyPublic.encode())
      );
      return properties;
    }
  }

  private static final class NPAgentKeyPublicEd448
    implements NPAgentKeyPublicEd448Type
  {
    private final EdECPublicKey keyPublic;

    NPAgentKeyPublicEd448(
      final EdECPublicKey inKeyPublic)
    {
      this.keyPublic =
        Objects.requireNonNull(inKeyPublic, "keyPublic");
    }

    @Override
    public boolean equals(
      final Object o)
    {
      if (this == o) {
        return true;
      }
      if (o == null || !this.getClass().equals(o.getClass())) {
        return false;
      }
      final NPAgentKeyPublicEd448 that = (NPAgentKeyPublicEd448) o;
      return Objects.equals(this.asText(), that.asText());
    }

    @Override
    public int hashCode()
    {
      return Objects.hash(this.asText());
    }

    @Override
    public NPAgentKeyID id()
    {
      return new NPAgentKeyID(HEX.formatHex(this.encode()));
    }

    @Override
    public String toString()
    {
      return "[NPAgentKeyPublicEd448 %s]".formatted(this.id());
    }

    @Override
    public boolean verifyData(
      final NPSignedData signed)
      throws NPException
    {
      Objects.requireNonNull(signed, "signed");

      try {
        final var signature = Signature.getInstance(ED_448);
        signature.initVerify(this.keyPublic);
        signature.update(signed.data());
        return signature.verify(signed.signature());
      } catch (final GeneralSecurityException e) {
        throw new NPException(
          e.getMessage(),
          e,
          NPStandardErrorCodes.errorSignatureVerificationFailed(),
          Map.of(),
          Optional.empty()
        );
      }
    }

    @Override
    public byte[] asBytes()
    {
      return this.encode();
    }

    public byte[] encode()
    {
      try (var output = new ByteArrayOutputStream()) {
        final var point = this.keyPublic.getPoint();
        output.write(point.isXOdd() ? 1 : 0);
        output.write(point.getY().toByteArray());
        output.flush();
        return output.toByteArray();
      } catch (final IOException e) {
        throw new UncheckedIOException(e);
      }
    }
  }

  private static final class NPAgentKeyPrivateEd448
    implements NPAgentKeyPrivateEd448Type
  {
    private final EdECPrivateKey keyPrivate;

    NPAgentKeyPrivateEd448(
      final EdECPrivateKey inKeyPrivate)
    {
      this.keyPrivate =
        Objects.requireNonNull(inKeyPrivate, "keyPrivate");
    }

    @Override
    public boolean equals(final Object o)
    {
      if (this == o) {
        return true;
      }
      if (o == null || !this.getClass().equals(o.getClass())) {
        return false;
      }
      final NPAgentKeyPrivateEd448 that = (NPAgentKeyPrivateEd448) o;
      return Objects.equals(this.asText(), that.asText());
    }

    @Override
    public String toString()
    {
      return "[NPAgentKeyPrivateEd448 0x%x]"
        .formatted(Integer.valueOf(this.hashCode()));
    }

    @Override
    public int hashCode()
    {
      return Objects.hash(this.asText());
    }

    @Override
    public byte[] signData(
      final byte[] data)
      throws NPException
    {
      Objects.requireNonNull(data, "data");

      try {
        final var signature = Signature.getInstance(ED_448);
        signature.initSign(this.keyPrivate);
        signature.update(data);
        return signature.sign();
      } catch (final GeneralSecurityException e) {
        throw new NPException(
          e.getMessage(),
          e,
          NPStandardErrorCodes.errorSignatureCreationFailed(),
          Map.of(),
          Optional.empty()
        );
      }
    }

    @Override
    public String asText()
    {
      return HEX.formatHex(this.keyPrivate.getEncoded());
    }
  }
}
