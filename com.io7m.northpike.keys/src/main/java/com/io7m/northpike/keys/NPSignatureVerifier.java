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


package com.io7m.northpike.keys;

import com.io7m.jaffirm.core.Invariants;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPublicKey;
import org.bouncycastle.openpgp.PGPCompressedData;
import org.bouncycastle.openpgp.PGPException;
import org.bouncycastle.openpgp.PGPPublicKey;
import org.bouncycastle.openpgp.PGPSignature;
import org.bouncycastle.openpgp.PGPSignatureList;
import org.bouncycastle.openpgp.PGPUtil;
import org.bouncycastle.openpgp.jcajce.JcaPGPObjectFactory;
import org.bouncycastle.openpgp.jcajce.JcaPGPPublicKeyRingCollection;
import org.bouncycastle.openpgp.operator.jcajce.JcaPGPContentVerifierBuilderProvider;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.MDC;

import java.io.ByteArrayInputStream;
import java.util.HexFormat;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorSignatureVerificationFailed;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * The default signature verifier.
 */

public final class NPSignatureVerifier implements NPSignatureVerifierType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPSignatureVerifier.class);

  private final NPSignatureKeyLookupType lookup;
  private final byte[] data;
  private final byte[] signatureData;

  private NPSignatureVerifier(
    final NPSignatureKeyLookupType inLookup,
    final byte[] inData,
    final byte[] inSignatureData)
  {
    this.lookup =
      Objects.requireNonNull(inLookup, "lookup");
    this.data =
      Objects.requireNonNull(inData, "data");
    this.signatureData =
      Objects.requireNonNull(inSignatureData, "signatureData");
  }

  /**
   * @return A new signature verifier builder
   */

  public static NPSignatureVerifierBuilderType builder()
  {
    return new Builder();
  }

  @Override
  public NPPublicKey verify()
    throws NPException
  {
    final var signature =
      findSignature(this.signatureData);

    if (signature == null) {
      throw errorNoUsableSignature();
    }

    final var fingerprint =
      findSignatureFingerprint(signature);

    if (fingerprint == null) {
      throw errorNoFingerprint();
    }

    MDC.put("Key", fingerprint.value());
    final var key = this.lookup.keyFor(fingerprint);

    Invariants.checkInvariantV(
      Objects.equals(key.fingerprint(), fingerprint),
      "Returned key fingerprint %s must match fingerprint %s",
      key.fingerprint(),
      fingerprint
    );

    this.verifyDataUsingKey(key, signature);
    return key;
  }

  private void verifyDataUsingKey(
    final NPPublicKey key,
    final PGPSignature signature)
    throws NPException
  {
    try {
      final var bcKey = convertPublicKeyToBC(key);
      signature.init(new JcaPGPContentVerifierBuilderProvider(), bcKey);
      signature.update(this.data);

      final var verified = signature.verify();
      if (!verified) {
        throw errorSignatureInvalid();
      }
    } catch (final PGPException e) {
      throw errorSignatureInvalid(e);
    }
  }

  private static PGPPublicKey convertPublicKeyToBC(
    final NPPublicKey key)
    throws NPException
  {
    final var stream =
      new ByteArrayInputStream(key.encodedForm().getBytes(UTF_8));

    try (var decoder = PGPUtil.getDecoderStream(stream)) {
      final var keyRingCollection =
        new JcaPGPPublicKeyRingCollection(decoder);
      final var keyRings =
        keyRingCollection.getKeyRings();

      while (keyRings.hasNext()) {
        final var keyRing =
          keyRings.next();
        final var keys =
          keyRing.getPublicKeys();

        while (keys.hasNext()) {
          return keys.next();
        }
      }
    } catch (final Exception e) {
      throw errorPublicKeyDecodeFailed(e);
    }

    throw errorPublicKeyDecodeFailed();
  }

  private static NPException errorSignatureInvalid(
    final Exception e)
  {
    return new NPException(
      "The data could not be verified against the given signature.",
      e,
      errorSignatureVerificationFailed(),
      Map.of(),
      Optional.empty()
    );
  }

  private static NPException errorSignatureInvalid()
  {
    return new NPException(
      "The data could not be verified against the given signature.",
      errorSignatureVerificationFailed(),
      Map.of(),
      Optional.empty()
    );
  }

  private static NPException errorPublicKeyDecodeFailed(
    final Exception e)
  {
    return new NPException(
      "Could not correctly decode the given public key.",
      e,
      errorSignatureVerificationFailed(),
      Map.of(),
      Optional.empty()
    );
  }

  private static NPException errorPublicKeyDecodeFailed()
  {
    return new NPException(
      "Could not correctly decode the given public key.",
      errorSignatureVerificationFailed(),
      Map.of(),
      Optional.empty()
    );
  }

  private static NPException errorNoFingerprint()
  {
    return new NPException(
      "Signature data did not contain a usable PGP key fingerprint.",
      errorSignatureVerificationFailed(),
      Map.of(),
      Optional.empty()
    );
  }

  private static NPException errorNoUsableSignature()
  {
    return new NPException(
      "Signature data did not contain a usable PGP signature.",
      errorSignatureVerificationFailed(),
      Map.of(),
      Optional.empty()
    );
  }

  private static NPFingerprint findSignatureFingerprint(
    final PGPSignature signature)
  {
    final var packets =
      signature.getHashedSubPackets();

    if (packets == null) {
      LOG.debug("Signature data did not contain any hashed subpackets.");
      return null;
    }

    final var fingerprintPacket =
      packets.getIssuerFingerprint();

    if (fingerprintPacket == null) {
      LOG.debug("Signature data did not contain a fingerprint subpacket.");
      return null;
    }

    return new NPFingerprint(
      HexFormat.of().formatHex(fingerprintPacket.getFingerprint())
    );
  }

  private static PGPSignature findSignature(
    final byte[] signatureData)
    throws NPException
  {
    try {
      final var signatureInputStream =
        new ByteArrayInputStream(signatureData);
      final var signatureDecoder =
        PGPUtil.getDecoderStream(signatureInputStream);

      return findSignatureInObjectFactory(
        new JcaPGPObjectFactory(signatureDecoder)
      );
    } catch (final Exception e) {
      throw new NPException(
        e.getMessage(),
        e,
        errorSignatureVerificationFailed(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  private static PGPSignature findSignatureInObjectFactory(
    final JcaPGPObjectFactory objectFactory)
    throws PGPException
  {
    final var pgpIter =
      objectFactory.iterator();

    while (pgpIter.hasNext()) {
      final var pgpObject = pgpIter.next();
      if (pgpObject instanceof final PGPSignature signature) {
        return signature;
      }

      if (pgpObject instanceof final PGPCompressedData compressedData) {
        final var nextObjectFactory =
          new JcaPGPObjectFactory(compressedData.getDataStream());
        final var signature =
          findSignatureInObjectFactory(nextObjectFactory);
        if (signature != null) {
          return signature;
        }
      }

      if (pgpObject instanceof final PGPSignatureList list) {
        return list.get(0);
      }
    }

    return null;
  }

  private static final class Builder implements NPSignatureVerifierBuilderType
  {
    private NPSignatureKeyLookupType keyLookup;
    private byte[] data;
    private byte[] signatureData;

    private Builder()
    {

    }

    @Override
    public NPSignatureVerifierBuilderType setKeyLookup(
      final NPSignatureKeyLookupType lookup)
    {
      this.keyLookup =
        Objects.requireNonNull(lookup, "lookup");
      return this;
    }

    @Override
    public NPSignatureVerifierBuilderType setData(
      final byte[] inData)
    {
      this.data =
        Objects.requireNonNull(inData, "data");
      return this;
    }

    @Override
    public NPSignatureVerifierBuilderType setSignature(
      final byte[] inSignatureData)
    {
      this.signatureData =
        Objects.requireNonNull(inSignatureData, "inSignatureData");
      return this;
    }

    @Override
    public NPSignatureVerifierType build()
    {
      return new NPSignatureVerifier(
        this.keyLookup,
        this.data,
        this.signatureData
      );
    }
  }
}
