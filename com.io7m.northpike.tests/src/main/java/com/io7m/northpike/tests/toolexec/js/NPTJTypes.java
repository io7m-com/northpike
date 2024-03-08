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


package com.io7m.northpike.tests.toolexec.js;

import com.io7m.northpike.toolexec.api.NPTException;
import com.io7m.northpike.toolexec.js.NPTJSLanguageProvider;
import com.io7m.northpike.toolexec.program.api.NPTPContextType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.UUID;
import java.util.stream.Collectors;

public final class NPTJTypes
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPTJTypes.class);

  private NPTJTypes()
  {

  }

  public static void main(
    final String[] args)
    throws IOException, NPTException
  {
    final var context =
      NPTPContextType.class;
    final var methods =
      context.getMethods();

    for (final var method : methods) {
      final var file =
        Paths.get("/tmp/txjs-%s.xml".formatted(method.getName()));

      try (var writer = Files.newBufferedWriter(file)) {
        writer.append(
          """
            <?xml version="1.0" encoding="UTF-8"?>

            <Section xmlns="urn:com.io7m.structural:8:0"
                     id="%s"
                     title="%s">
              <Subsection title="Name">
                <Paragraph>
                  <Term type="function">%s</Term>
                </Paragraph>
                <Paragraph>
                  Do something.
                </Paragraph>
              </Subsection>
              <Subsection title="Description">
                <Paragraph>
                  The <Term type="function">%s</Term> function...
                </Paragraph>
              </Subsection>
            </Section>
            """
            .formatted(
              UUID.nameUUIDFromBytes(method.getName().getBytes(StandardCharsets.UTF_8)),
              method.getName(),
              formatType(method),
              method.getName()
            )
        );
        writer.flush();
      }
    }
  }

  private static String formatType(
    final Method method)
  {
    final var b = new StringBuilder();
    b.append(method.getName());
    b.append(" (");
    b.append(
      Arrays.stream(method.getParameterTypes())
        .map(Class::getSimpleName)
        .collect(Collectors.joining(", "))
    );
    b.append(") → ");
    b.append(method.getReturnType().getSimpleName());
    return b.toString();
  }
}
