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


package com.io7m.northpike.agent.internal;

import com.io7m.jattribute.core.AttributeType;
import com.io7m.jattribute.core.Attributes;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentConnectionStatus;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.connections.NPMessageConnectionAbstract;
import com.io7m.northpike.connections.NPMessageHandlerType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPACommandType;
import com.io7m.northpike.protocol.agent.NPAEventType;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseError;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.protocol.agent.NPAResponseType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;

import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.AUTHENTICATED;
import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.AUTHENTICATING;
import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.AUTHENTICATION_FAILED;
import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.CONNECTED;
import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.CONNECTING;
import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.CONNECTION_FAILED;
import static com.io7m.northpike.agent.internal.NPAgentExceptions.errorUnexpectedMessage;

/**
 * An agent connection.
 */

public final class NPAgentConnection
  extends NPMessageConnectionAbstract<NPAMessageType, NPAResponseType>
  implements NPAgentConnectionType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentConnection.class);

  private final AttributeType<NPAgentConnectionStatus> status;
  private final NPAgentConfiguration configuration;

  NPAgentConnection(
    final NPAgentConfiguration inConfiguration)
  {
    super(
      LOG,
      CloseableCollection.create(() -> {
        return new NPAgentException(
          "One or more resources could not be closed.",
          new NPErrorCode("resources"),
          Map.of(),
          Optional.empty()
        );
      })
    );

    this.configuration =
      Objects.requireNonNull(inConfiguration, "inConfiguration");

    this.status =
      Attributes.create(e -> LOG.error("Event handling error: ", e))
        .create(CONNECTING);

    this.status.subscribe((oldValue, newValue) -> {
      LOG.debug("Agent connection {} -> {}", oldValue, newValue);
    });
  }

  @Override
  public AttributeType<NPAgentConnectionStatus> status()
  {
    return this.status;
  }

  @Override
  public <R extends NPAResponseType> CompletableFuture<R> submitCommand(
    final NPACommandType<R> command)
  {
    return this.submitExpectingResponse(command)
      .thenApply(x -> (R) x);
  }

  @Override
  public void submitResponse(
    final NPAResponseType response)
  {
    this.submitExpectingNoResponse(response);
  }

  @Override
  public void submitEvent(
    final NPAEventType event)
  {
    this.submitExpectingNoResponse(event);
  }

  @Override
  protected UUID onFindMessageID(
    final NPAMessageType message)
  {
    return message.messageID();
  }

  @Override
  protected UUID onFindCorrelationID(
    final NPAResponseType message)
  {
    return message.correlationID();
  }

  @Override
  protected NPMessageHandlerType<NPAMessageType> onConnect()
    throws NPException
  {
    this.status.set(CONNECTING);
    LOG.info(
      "Connecting to {}:{}",
      this.configuration.remoteAddress(),
      this.configuration.remotePort()
    );

    final NPAgentConnectionHandlerType newHandler;
    final var strings = this.configuration.strings();
    try {
      newHandler = NPAgentConnectionHandlers.openConnection(this.configuration);
    } catch (final IOException e) {
      this.status.set(CONNECTION_FAILED);
      throw NPAgentExceptions.errorIO(strings, e);
    }

    this.resources().add(newHandler);
    this.status.set(CONNECTED);

    final var oldHandler =
      this.existingHandler();

    try {
      if (oldHandler != null) {
        oldHandler.close();
      }
    } catch (final NPAgentException e) {
      LOG.warn("Unable to close old connection: ", e);
      this.exceptionsPublisher().submit(e);
    }

    this.status.set(AUTHENTICATING);
    newHandler.send(NPACommandCLogin.of(this.configuration.accessKey()));

    while (!this.isClosed()) {
      final var responseOpt = newHandler.receive();
      if (responseOpt.isPresent()) {
        final var response = responseOpt.get();
        if (response instanceof final NPAResponseError error) {
          this.status.set(AUTHENTICATION_FAILED);
          throw new NPAgentException(
            error.message(),
            error.errorCode(),
            error.attributes(),
            Optional.empty()
          );
        }

        if (response instanceof NPAResponseOK) {
          this.status.set(AUTHENTICATED);
          return newHandler;
        }

        this.status.set(AUTHENTICATION_FAILED);
        throw errorUnexpectedMessage(strings, NPAResponseOK.class, response);
      }
    }

    return null;
  }

  @Override
  protected NPAResponseType onCheckIfMessageIsResponse(
    final NPAMessageType message)
  {
    if (message instanceof final NPAResponseType response) {
      return response;
    }
    return null;
  }
}
