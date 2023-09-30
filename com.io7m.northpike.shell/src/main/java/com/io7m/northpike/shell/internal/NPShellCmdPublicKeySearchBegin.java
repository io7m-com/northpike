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

package com.io7m.northpike.shell.internal;

import com.io7m.northpike.keys.NPPublicKeys;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPPublicKeySearchParameters;
import com.io7m.northpike.model.NPValidityException;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeySearchBegin;
import com.io7m.northpike.protocol.user.NPUResponsePublicKeySearch;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "public-key-search-begin"
 */

public final class NPShellCmdPublicKeySearchBegin
  extends NPShellCmdAbstractCR<NPUCommandPublicKeySearchBegin, NPUResponsePublicKeySearch>
{
  private static final QParameterNamed1<Integer> LIMIT =
    new QParameterNamed1<>(
      "--limit",
      List.of(),
      new QConstant("The maximum number of results per page."),
      Optional.of(Integer.valueOf(10)),
      Integer.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdPublicKeySearchBegin(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "public-key-search-begin",
        new QConstant("Begin searching for public keys."),
        Optional.empty()
      ),
      NPUCommandPublicKeySearchBegin.class,
      NPUResponsePublicKeySearch.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      LIMIT
    );
  }

  @Override
  protected NPUCommandPublicKeySearchBegin onCreateCommand(
    final QCommandContextType context)
  {
    final var parameters =
      new NPPublicKeySearchParameters(
        context.parameterValue(LIMIT).longValue()
      );

    return new NPUCommandPublicKeySearchBegin(UUID.randomUUID(), parameters);
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponsePublicKeySearch response)
    throws Exception
  {
    final var parsedPage =
      response.results()
        .map(x -> {
          try {
            return NPPublicKeys.decodeString(x).get(0);
          } catch (final NPException e) {
            throw new NPValidityException(e.getMessage(), e);
          }
        });

    this.formatter().formatPublicKeySummaries(parsedPage);
  }
}
