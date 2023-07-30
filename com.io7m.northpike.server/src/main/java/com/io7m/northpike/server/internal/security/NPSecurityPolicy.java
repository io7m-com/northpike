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

package com.io7m.northpike.server.internal.security;

import com.io7m.anethum.api.ParseStatus;
import com.io7m.anethum.api.ParsingException;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.vanilla.MPolicyParsers;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.URI;
import java.util.Set;

/**
 * The security policy objects.
 */

public final class NPSecurityPolicy
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPSecurityPolicy.class);

  /**
   * An all-powerful administrator of servers.
   */

  public static final MRoleName ROLE_SERVER_ADMIN =
    MRoleName.of("server.admin");

  /**
   * All roles.
   */

  public static final Set<MRoleName> ROLES_ALL =
    Set.of(
      ROLE_SERVER_ADMIN
    );

  /**
   * Load the internal security policy.
   *
   * @return A policy
   *
   * @throws IOException On errors
   */

  public static MPolicy open()
    throws IOException
  {
    final var parsers = new MPolicyParsers();

    final var resource =
      "/com/io7m/northpike/security/Policy.mp";
    try (var stream =
           NPSecurityPolicy.class.getResourceAsStream(resource)) {
      final var source = URI.create(resource);
      try (var parser =
             parsers.createParser(
               source,
               stream,
               NPSecurityPolicy::logStatus)) {
        return parser.execute();
      } catch (final ParsingException e) {
        LOG.error("One or more parse errors were encountered.");
        throw new IOException(e.getMessage(), e);
      }
    }
  }

  private static void logStatus(
    final ParseStatus status)
  {
    switch (status.severity()) {
      case PARSE_ERROR -> {
        LOG.error(
          "{}:{}: {}: {}",
          Integer.valueOf(status.lexical().line()),
          Integer.valueOf(status.lexical().column()),
          status.errorCode(),
          status.message()
        );

        for (final var entry : status.attributes().entrySet()) {
          LOG.error("  {}: {}", entry.getKey(), entry.getValue());
        }
      }
      case PARSE_WARNING -> {
        LOG.warn(
          "{}:{}: {}: {}",
          Integer.valueOf(status.lexical().line()),
          Integer.valueOf(status.lexical().column()),
          status.errorCode(),
          status.message()
        );

        for (final var entry : status.attributes().entrySet()) {
          LOG.warn("  {}: {}", entry.getKey(), entry.getValue());
        }
      }
      case PARSE_INFO -> {
        LOG.info(
          "{}:{}: {}: {}",
          Integer.valueOf(status.lexical().line()),
          Integer.valueOf(status.lexical().column()),
          status.errorCode(),
          status.message()
        );

        for (final var entry : status.attributes().entrySet()) {
          LOG.info("  {}: {}", entry.getKey(), entry.getValue());
        }
      }
    }
  }

  private NPSecurityPolicy()
  {

  }
}
