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


package com.io7m.northpike.toolexec.api;

import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.toolexec.program.api.NPTPVariableType;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.ServiceLoader;
import java.util.stream.Collectors;

import static com.io7m.northpike.strings.NPStringConstants.FORMAT;
import static com.io7m.northpike.strings.NPStringConstants.TOOLEXEC_NO_SUCH_LANGUAGE;
import static com.io7m.northpike.strings.NPStringConstants.TOOLEXEC_PROVIDER_INDEXED;

/**
 * Tool execution evaluation service.
 */

public final class NPTPEvaluationService
  implements NPTEvaluationServiceType
{
  private final NPStrings strings;
  private final List<NPTEvaluationLanguageProviderType> languageProviders;

  private NPTPEvaluationService(
    final NPStrings inStrings,
    final List<NPTEvaluationLanguageProviderType> inLanguageProviders)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.languageProviders =
      Objects.requireNonNull(inLanguageProviders, "languageProviders");
  }

  /**
   * Create a service.
   *
   * @param inStrings           The string resources
   * @param inLanguageProviders The language providers
   *
   * @return A service
   */

  public static NPTEvaluationServiceType create(
    final NPStrings inStrings,
    final List<NPTEvaluationLanguageProviderType> inLanguageProviders)
  {
    return new NPTPEvaluationService(inStrings, inLanguageProviders);
  }

  /**
   * Create a service, finding language providers in {@code ServiceLoader}.
   *
   * @param inStrings The string resources
   *
   * @return A service
   */

  public static NPTEvaluationServiceType createFromServiceLoader(
    final NPStrings inStrings)
  {
    return new NPTPEvaluationService(
      inStrings,
      ServiceLoader.load(NPTEvaluationLanguageProviderType.class)
        .stream()
        .map(ServiceLoader.Provider::get)
        .collect(Collectors.toList())
    );
  }

  @Override
  public NPTEvaluableType create(
    final NPFormatName formatName,
    final Map<String, String> initialEnvironment,
    final List<NPTPVariableType> variables,
    final String program)
    throws NPTException
  {
    Objects.requireNonNull(formatName, "formatName");
    Objects.requireNonNull(initialEnvironment, "initialEnvironment");
    Objects.requireNonNull(variables, "variables");
    Objects.requireNonNull(program, "program");

    for (final var languageProvider : this.languageProviders) {
      if (Objects.equals(languageProvider.languageSupported(), formatName)) {
        return languageProvider.create(initialEnvironment, variables, program);
      }
    }

    throw this.errorNoSuchLanguageProvider(formatName);
  }

  private NPTException errorNoSuchLanguageProvider(
    final NPFormatName formatName)
  {
    final var attributes = new HashMap<String, String>();
    for (int index = 0; index < this.languageProviders.size(); ++index) {
      final var provider = this.languageProviders.get(index);
      attributes.put(
        this.strings.format(TOOLEXEC_PROVIDER_INDEXED, index),
        provider.languageSupported().toString()
      );
    }

    attributes.put(this.strings.format(FORMAT), formatName.toString());
    return new NPTException(
      this.strings.format(TOOLEXEC_NO_SUCH_LANGUAGE),
      NPStandardErrorCodes.errorToolExecutionFailed(),
      attributes,
      Optional.empty(),
      List.of()
    );
  }

  @Override
  public String description()
  {
    return "Tool execution evaluation service.";
  }
}
