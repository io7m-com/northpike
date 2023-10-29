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


package com.io7m.northpike.agent.workexec.main.internal;

import ch.qos.logback.classic.spi.ILoggingEvent;
import ch.qos.logback.classic.spi.IThrowableProxy;
import ch.qos.logback.classic.spi.StackTraceElementProxy;
import ch.qos.logback.core.AppenderBase;
import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBProtocolMessageVersionedSerializerType;
import com.io7m.cedarbridge.runtime.api.CBSerializationContextType;
import com.io7m.cedarbridge.runtime.api.CBString;
import com.io7m.cedarbridge.runtime.bssio.CBSerializationContextBSSIO;
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.cedarbridge.runtime.time.CBOffsetDateTime;
import com.io7m.jaffirm.core.Invariants;
import com.io7m.jbssio.vanilla.BSSWriters;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.agent.workexec.local.NPWEMessages;
import com.io7m.northpike.agent.workexec.local.cb.NWEException;
import com.io7m.northpike.agent.workexec.local.cb.NWEHeader;
import com.io7m.northpike.agent.workexec.local.cb.NWEOutput;
import com.io7m.northpike.agent.workexec.local.cb.NWEStackTraceElement;
import com.io7m.northpike.agent.workexec.local.cb.ProtocolNWE;
import com.io7m.northpike.agent.workexec.local.cb.ProtocolNWEType;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.NPStoredStackTraceElement;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.UncheckedIOException;
import java.time.OffsetDateTime;
import java.time.ZoneId;
import java.util.Arrays;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.locks.ReentrantLock;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;
import static java.util.Objects.requireNonNullElse;

/**
 * A binary logger.
 */

public final class NPWELoggerBinary
  extends AppenderBase<ILoggingEvent>
  implements NPWELoggerType
{
  private static final ProtocolNWE PROTOCOL =
    new ProtocolNWE();
  private static final BSSWriters WRITERS =
    new BSSWriters();
  private static final ZoneId UTC =
    ZoneId.of("UTC");

  private final OutputStream output;
  private final CBProtocolMessageVersionedSerializerType<ProtocolNWEType> outputSerializer;
  private final ReentrantLock outputLock;

  private NPWELoggerBinary(
    final OutputStream inOutput)
  {
    this.output =
      Objects.requireNonNull(inOutput, "output");
    this.outputSerializer =
      PROTOCOL.serializerForProtocolVersion(1L)
        .orElseThrow();
    this.outputLock =
      new ReentrantLock();
  }

  /**
   * Create a new binary logger.
   *
   * @param output The output stream
   *
   * @return The binary logger
   */

  public static NPWELoggerType create(
    final OutputStream output)
  {
    return new NPWELoggerBinary(output);
  }

  private static CBSerializationContextType createContext(
    final ByteArrayOutputStream o)
  {
    return CBSerializationContextBSSIO.createFromOutputStream(WRITERS, o);
  }

  private static NWEException convertProxyToNWEException(
    final IThrowableProxy proxy)
  {
    return new NWEException(
      string(proxy.getClassName()),
      string(requireNonNullElse(proxy.getMessage(), "")),
      CBMaps.ofMapString(Map.of()),
      CBOptionType.fromOptional(
        Optional.ofNullable(proxy.getCause())
          .map(NPWELoggerBinary::convertProxyToNWEException)
      ),
      CBLists.ofCollection(
        Arrays.asList(proxy.getSuppressed()),
        NPWELoggerBinary::convertProxyToNWEException
      ),
      CBLists.ofCollection(
        Arrays.asList(proxy.getStackTraceElementProxyArray()),
        NPWELoggerBinary::convertProxyToNWEStackTrace
      )
    );
  }

  private static NWEStackTraceElement convertProxyToNWEStackTrace(
    final StackTraceElementProxy e)
  {
    return convertToNWEStackTrace(
      NPStoredStackTraceElement.ofElement(e.getStackTraceElement())
    );
  }

  private static NWEException convertToNWEException(
    final NPStoredException ex)
  {
    return NPWEMessages.exceptionToWire(ex);
  }

  private static NWEStackTraceElement convertToNWEStackTrace(
    final NPStoredStackTraceElement e)
  {
    return new NWEStackTraceElement(
      string(e.classLoader()),
      string(e.moduleName()),
      string(e.moduleVersion()),
      string(e.declaringClass()),
      string(e.methodName()),
      string(e.fileName()),
      unsigned32(e.lineNumber())
    );
  }

  @Override
  public void initialize()
    throws IOException
  {
    final var header =
      new NWEHeader(
        unsigned32(0x4e505745),
        unsigned32(1L)
      );

    final byte[] data;
    try (var o = new ByteArrayOutputStream()) {
      final var c = createContext(o);
      NWEHeader.serialize(c, header);
      c.flush();
      data = o.toByteArray();
    }

    this.outputLock.lock();
    try {
      this.output.write(data);
      this.output.flush();
    } finally {
      this.outputLock.unlock();
    }
  }

  @Override
  public void logStatusEvent(
    final ILoggingEvent event)
    throws IOException
  {
    final var nweException =
      Optional.ofNullable(event.getThrowableProxy())
        .map(NPWELoggerBinary::convertProxyToNWEException);

    final var message =
      new NWEOutput(
        new CBOffsetDateTime(OffsetDateTime.ofInstant(event.getInstant(), UTC)),
        CBMaps.ofMapString(event.getMDCPropertyMap()),
        new CBString(event.getFormattedMessage()),
        CBOptionType.fromOptional(nweException)
      );

    this.writeMessage(message);
  }

  private void writeMessage(
    final NWEOutput message)
    throws IOException
  {
    final byte[] messageData;
    try (var o = new ByteArrayOutputStream()) {
      final var c = createContext(o);
      this.outputSerializer.serialize(c, message);
      c.flush();
      messageData = o.toByteArray();
    }

    Invariants.checkInvariantI(
      messageData.length,
      messageData.length != 0,
      "Length %d must not be 0"::formatted
    );

    final byte[] lengthData;
    try (var o = new ByteArrayOutputStream()) {
      final var c = createContext(o);
      c.writeU32(Integer.toUnsignedLong(messageData.length));
      c.flush();
      lengthData = o.toByteArray();
    }

    Invariants.checkInvariantI(
      lengthData.length,
      lengthData.length == 4,
      "Length %d must be 4"::formatted
    );

    this.outputLock.lock();
    try {
      this.output.write(lengthData);
      this.output.write(messageData);
      this.output.flush();
    } finally {
      this.outputLock.unlock();
    }
  }

  @Override
  public void logWorkEvent(
    final NPAWorkEvent event)
    throws IOException
  {
    final var nweException =
      event.exception()
        .map(NPWELoggerBinary::convertToNWEException);

    final var message =
      new NWEOutput(
        new CBOffsetDateTime(event.time()),
        CBMaps.ofMapString(event.attributes()),
        new CBString(event.message()),
        CBOptionType.fromOptional(nweException)
      );

    this.writeMessage(message);
  }

  @Override
  protected void append(
    final ILoggingEvent event)
  {
    try {
      this.logStatusEvent(event);
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
  }
}
