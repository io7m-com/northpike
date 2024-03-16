/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.shell.commons;

import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * The default confirmation service.
 */

public final class NPShellConfirmationService
  implements NPShellConfirmationServiceType
{
  private final ConcurrentHashMap<UUID, NPShellConfirmationRequired> confirmations;
  private final ConcurrentLinkedQueue<UUID> nextIds;

  /**
   * The default confirmation service.
   */

  public NPShellConfirmationService()
  {
    this.confirmations =
      new ConcurrentHashMap<>();
    this.nextIds =
      new ConcurrentLinkedQueue<>();
  }

  @Override
  public void confirm(
    final UUID value)
    throws Exception
  {
    final var existing = this.confirmations.get(value);
    if (existing == null) {
      throw new NPShellConfirmationMissing();
    }
    this.confirmations.remove(value);
    existing.operation().execute();
  }

  @Override
  public NPShellConfirmationRequired register(
    final NPShellConfirmationRequest request)
  {
    final var id =
      Optional.ofNullable(this.nextIds.poll())
        .orElse(UUID.randomUUID());

    final var required =
      new NPShellConfirmationRequired(
        request.command(),
        id,
        request.operation()
      );

    this.confirmations.put(id, required);
    return required;
  }

  @Override
  public void setNextConfirmationId(
    final UUID confirmationId)
  {
    this.nextIds.add(
      Objects.requireNonNull(confirmationId, "confirmationId")
    );
  }

  @Override
  public String toString()
  {
    return "[NPShellConfirmationService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }

  @Override
  public String description()
  {
    return "Shell confirmation service.";
  }
}
