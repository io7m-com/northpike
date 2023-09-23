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


package com.io7m.northpike.repository.jgit.internal;

import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.keys.NPSignatureKeyLookupType;
import com.io7m.northpike.keys.NPSignatureVerifier;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPPublicKey;
import org.eclipse.jgit.lib.GpgConfig;
import org.eclipse.jgit.lib.GpgSignatureVerifier;
import org.eclipse.jgit.revwalk.RevCommit;
import org.eclipse.jgit.revwalk.RevObject;
import org.eclipse.jgit.util.RawParseUtils;
import org.slf4j.MDC;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Date;
import java.util.Objects;

/**
 * An adapter from JGit's signature verifier to the plain BC verifier.
 */

public final class NPSCMJGVerifier implements GpgSignatureVerifier
{
  private static final byte[] GPG_HEADER =
    {'g', 'p', 'g', 's', 'i', 'g'};

  private final NPSignatureKeyLookupType keys;
  private final NPCommitUnqualifiedID commitId;
  private final NPClockServiceType clock;
  private NPPublicKey keyUsed;

  /**
   * An adapter from JGit's signature verifier to the plain BC verifier.
   *
   * @param inCommitId The commit being verified
   * @param inClock    The clock
   * @param inKeys     The key lookup
   */

  public NPSCMJGVerifier(
    final NPCommitUnqualifiedID inCommitId,
    final NPSignatureKeyLookupType inKeys,
    final NPClockServiceType inClock)
  {
    this.commitId =
      Objects.requireNonNull(inCommitId, "commitId");
    this.keys =
      Objects.requireNonNull(inKeys, "keys");
    this.clock =
      Objects.requireNonNull(inClock, "clock");
  }

  @Override
  public SignatureVerification verifySignature(
    final RevObject object,
    final GpgConfig config)
    throws IOException
  {
    Objects.requireNonNull(object, "object");
    Objects.requireNonNull(config, "config");

    MDC.put("Commit", this.commitId.value());

    if (object instanceof final RevCommit commit) {
      final var signatureData = commit.getRawGpgSignature();
      if (signatureData == null) {
        throw new IOException("Commit has no signature.");
      }

      final var raw =
        commit.getRawBuffer();

      /*
       * Find out where the GPG signature header starts. The data included
       * in the signature is essentially all the headers minus the GPG
       * signature header. The signature header can appear in any order, so
       * we essentially need to strip the header out by writing any data
       * before the header to a temporary byte array, followed by any data
       * after the header.
       */

      final var gpgSigStart =
        RawParseUtils.headerStart(GPG_HEADER, raw, 0);
      final var gpgSigHeaderStart =
        (gpgSigStart - GPG_HEADER.length) - 1;

      final var inputData =
        new ByteArrayInputStream(raw);
      final var dataWithoutSignature =
        new ByteArrayOutputStream();

      /*
       * Write the leading data, skip the GPG signature, then write the
       * trailing data.
       */

      dataWithoutSignature.write(inputData.readNBytes(gpgSigHeaderStart));
      inputData.skipNBytes(GPG_HEADER.length);
      inputData.skipNBytes(1L);
      inputData.skipNBytes(signatureData.length);
      inputData.skipNBytes(1L);
      dataWithoutSignature.write(inputData.readAllBytes());
      return this.verify(dataWithoutSignature.toByteArray(), signatureData);
    }

    throw new UnsupportedOperationException();
  }

  @Override
  public SignatureVerification verify(
    final byte[] data,
    final byte[] signatureData)
    throws IOException
  {
    Objects.requireNonNull(data, "data");
    Objects.requireNonNull(signatureData, "signatureData");

    try {
      this.keyUsed =
        NPSignatureVerifier.builder()
          .setData(data)
          .setSignature(signatureData)
          .setKeyLookup(this.keys)
          .build()
          .verify();

      return new VerificationResult(
        new Date(this.keyUsed.timeCreated().toInstant().toEpochMilli()),
        this.keyUsed.userIDs().iterator().next(),
        this.keyUsed.fingerprint().value(),
        this.keyUsed.userIDs().iterator().next(),
        true,
        this.keyUsed.isExpired(this.clock.clock()),
        "VERIFIED"
      );
    } catch (final NPException e) {
      throw new IOException(e.getMessage(), e);
    }
  }

  @Override
  public String getName()
  {
    return "com.io7m.northpike.scm_repository.jgit";
  }

  @Override
  public void clear()
  {

  }

  /**
   * @return The key that was used for a successful verification
   */

  public NPPublicKey keyUsed()
  {
    return this.keyUsed;
  }

  private static final class VerificationResult implements SignatureVerification
  {
    private final Date creationDate;
    private final String signer;
    private final String keyUser;
    private final String fingerprint;
    private final boolean verified;
    private final boolean expired;
    private final String message;

    VerificationResult(
      final Date inCreationDate,
      final String inSigner,
      final String inFingerprint,
      final String inUser,
      final boolean inVerified,
      final boolean inExpired,
      final String inMessage)
    {
      this.creationDate =
        Objects.requireNonNull(inCreationDate, "creationDate");
      this.signer =
        Objects.requireNonNull(inSigner, "signer");
      this.fingerprint =
        Objects.requireNonNull(inFingerprint, "fingerprint");
      this.keyUser =
        Objects.requireNonNull(inUser, "user");
      this.verified =
        inVerified;
      this.expired =
        inExpired;
      this.message =
        Objects.requireNonNull(inMessage, "message");
    }

    @Override
    public Date getCreationDate()
    {
      return this.creationDate;
    }

    @Override
    public String getSigner()
    {
      return this.signer;
    }

    @Override
    public String getKeyUser()
    {
      return this.keyUser;
    }

    @Override
    public String getKeyFingerprint()
    {
      return this.fingerprint;
    }

    @Override
    public boolean isExpired()
    {
      return this.expired;
    }

    @Override
    public TrustLevel getTrustLevel()
    {
      return TrustLevel.FULL;
    }

    @Override
    public String getMessage()
    {
      return this.message;
    }

    @Override
    public boolean getVerified()
    {
      return this.verified;
    }
  }
}
