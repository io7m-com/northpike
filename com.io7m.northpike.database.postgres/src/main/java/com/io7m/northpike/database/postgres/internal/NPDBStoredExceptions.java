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


package com.io7m.northpike.database.postgres.internal;

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.bssio.CBSerializationContextBSSIO;
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.vanilla.BSSReaders;
import com.io7m.jbssio.vanilla.BSSWriters;
import com.io7m.northpike.database.postgres.internal.cb.NPDBException;
import com.io7m.northpike.database.postgres.internal.cb.NPDBStackTraceElement;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.NPStoredStackTraceElement;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.Optional;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;

/**
 * Functions to serialize/deserialize exceptions.
 */

public final class NPDBStoredExceptions
{
  private static final BSSWriterProviderType WRITERS =
    new BSSWriters();
  private static final BSSReaderProviderType READERS =
    new BSSReaders();

  private NPDBStoredExceptions()
  {

  }

  /**
   * Serialize an exception.
   *
   * @param exceptionOpt The optional exception
   *
   * @return The serialized exception, or null
   */

  public static byte[] serializeExceptionOptional(
    final Optional<NPStoredException> exceptionOpt)
  {
    return exceptionOpt.map(NPDBStoredExceptions::serializeException)
      .orElse(null);
  }

  /**
   * Serialize an exception.
   *
   * @param exception The exception
   *
   * @return The serialized exception, or null
   */

  public static byte[] serializeException(
    final NPStoredException exception)
  {
    try (var output = new ByteArrayOutputStream()) {
      final var context =
        CBSerializationContextBSSIO.createFromOutputStream(WRITERS, output);

      NPDBException.serialize(context, mapExceptionToWire(exception));
      context.flush();
      output.flush();
      return output.toByteArray();
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  private static NPDBStackTraceElement mapStackElementToWire(
    final NPStoredStackTraceElement e)
  {
    return new NPDBStackTraceElement(
      string(e.classLoader()),
      string(e.moduleName()),
      string(e.moduleVersion()),
      string(e.declaringClass()),
      string(e.methodName()),
      string(e.fileName()),
      unsigned32(e.lineNumber())
    );
  }

  private static NPDBException mapExceptionToWire(
    final NPStoredException e)
  {
    return new NPDBException(
      string(e.className()),
      string(e.message()),
      CBMaps.ofMapString(e.attributes()),
      CBOptionType.fromOptional(
        e.cause()
          .map(NPDBStoredExceptions::mapExceptionToWire)
      ),
      CBLists.ofCollection(
        e.suppressed(), NPDBStoredExceptions::mapExceptionToWire),
      CBLists.ofCollection(
        e.stackTrace(), NPDBStoredExceptions::mapStackElementToWire)
    );
  }

  /**
   * Deserialize an exception.
   *
   * @param data The data
   *
   * @return The deserialized exception, or null
   */

  public static NPStoredException deserializeException(
    final byte[] data)
  {
    final var context =
      CBSerializationContextBSSIO.createFromByteArray(READERS, data);

    try {
      return mapExceptionFromWire(NPDBException.deserialize(context));
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  private static NPStoredException mapExceptionFromWire(
    final NPDBException e)
  {
    return new NPStoredException(
      e.fieldClassName().value(),
      e.fieldMessage().value(),
      CBMaps.toMapString(e.fieldAttributes()),
      e.fieldCause()
        .asOptional()
        .map(NPDBStoredExceptions::mapExceptionFromWire),
      CBLists.toList(
        e.fieldSuppressed(),
        NPDBStoredExceptions::mapExceptionFromWire
      ),
      CBLists.toList(
        e.fieldStackTrace(),
        NPDBStoredExceptions::mapStackElementFromWire
      )
    );
  }

  private static NPStoredStackTraceElement mapStackElementFromWire(
    final NPDBStackTraceElement e)
  {
    return new NPStoredStackTraceElement(
      e.fieldClassLoader().value(),
      e.fieldModuleName().value(),
      e.fieldModuleVersion().value(),
      e.fieldDeclaringClass().value(),
      e.fieldMethodName().value(),
      e.fieldFileName().value(),
      (int) e.fieldLineNumber().value()
    );
  }
}
