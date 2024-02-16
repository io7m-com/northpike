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


package com.io7m.northpike.tests.documentation;

import com.io7m.medrina.api.MActionName;
import com.io7m.medrina.api.MObject;
import com.io7m.medrina.api.MRoleName;
import com.io7m.northpike.model.NPDocumentation;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.model.security.NPSecRole;
import org.w3c.dom.Document;
import org.w3c.dom.ls.DOMImplementationLS;
import org.w3c.dom.ls.LSSerializer;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.nio.file.Paths;

import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

public final class ShowSecurity
{
  private static final DocumentBuilderFactory DOCUMENTS =
    DocumentBuilderFactory.newDefaultNSInstance();
  private static final OpenOption[] OPEN_OPTIONS =
    {WRITE, CREATE, TRUNCATE_EXISTING};
  private static final String STRUCTURAL_8 =
    "urn:com.io7m.structural:8:0";

  private ShowSecurity()
  {

  }

  public static void main(
    final String[] args)
    throws Exception
  {
    final var outputDirectory =
      Paths.get(args[0]).toAbsolutePath();

    writeSecActions(outputDirectory);
    writeSecRoles(outputDirectory);
    writeSecObjects(outputDirectory);
  }

  private static void writeSecObjects(
    final Path outputDirectory)
    throws Exception
  {
    final var db =
      DOCUMENTS.newDocumentBuilder();
    final var doc =
      db.newDocument();
    final var root =
      doc.createElementNS(STRUCTURAL_8,"Table");

    root.setAttribute("type", "genericTable");
    doc.appendChild(root);

    final var cols = doc.createElementNS(STRUCTURAL_8,"Columns");
    root.appendChild(cols);

    final var col0 = doc.createElementNS(STRUCTURAL_8,"Column");
    col0.setTextContent("Name");
    cols.appendChild(col0);

    final var col1 = doc.createElementNS(STRUCTURAL_8,"Column");
    col1.setTextContent("Description");
    cols.appendChild(col1);

    for (final var f : NPSecObject.class.getFields()) {
      final var row = doc.createElementNS(STRUCTURAL_8,"Row");
      root.appendChild(row);

      final var c0 = doc.createElementNS(STRUCTURAL_8,"Cell");
      row.appendChild(c0);

      final var t = doc.createElementNS(STRUCTURAL_8,"Term");
      t.setAttribute("type", "expression");

      final MObject obj =
        (MObject) f.getDeclaringClass()
          .getMethod("object")
          .invoke(f.get(null));

      t.setTextContent(obj.type().value().toString());
      c0.appendChild(t);

      final var c1 = doc.createElementNS(STRUCTURAL_8,"Cell");
      row.appendChild(c1);

      c1.setTextContent(
        f.getAnnotation(NPDocumentation.class).value()
      );
    }

    serializeDocument(doc, outputDirectory.resolve("sec-objects.xml"));
  }

  private static void serializeDocument(
    final Document doc,
    final Path file)
    throws IOException
  {
    final var dom =
      (DOMImplementationLS) doc.getImplementation();
    final var serializer =
      dom.createLSSerializer();

    final var output =
      dom.createLSOutput();

    try (var writer = Files.newBufferedWriter(file, OPEN_OPTIONS)) {
      output.setCharacterStream(writer);
      output.setEncoding("UTF-8");
      serializer.write(doc, output);
    }
  }

  private static void writeSecRoles(
    final Path outputDirectory)
    throws Exception
  {
    final var db =
      DOCUMENTS.newDocumentBuilder();
    final var doc =
      db.newDocument();
    final var root =
      doc.createElementNS(STRUCTURAL_8,"Table");

    root.setAttribute("type", "genericTable");
    doc.appendChild(root);

    final var cols = doc.createElementNS(STRUCTURAL_8,"Columns");
    root.appendChild(cols);

    final var col0 = doc.createElementNS(STRUCTURAL_8,"Column");
    col0.setTextContent("Name");
    cols.appendChild(col0);

    final var col1 = doc.createElementNS(STRUCTURAL_8,"Column");
    col1.setTextContent("Description");
    cols.appendChild(col1);

    for (final var f : NPSecRole.class.getFields()) {
      final var row = doc.createElementNS(STRUCTURAL_8,"Row");
      root.appendChild(row);

      final var c0 = doc.createElementNS(STRUCTURAL_8,"Cell");
      row.appendChild(c0);

      final var t = doc.createElementNS(STRUCTURAL_8,"Term");
      t.setAttribute("type", "expression");

      final MRoleName name =
        (MRoleName) f.getDeclaringClass()
          .getMethod("role")
          .invoke(f.get(null));

      t.setTextContent(name.value().value());
      c0.appendChild(t);

      final var c1 = doc.createElementNS(STRUCTURAL_8,"Cell");
      row.appendChild(c1);

      c1.setTextContent(
        f.getAnnotation(NPDocumentation.class).value()
      );
    }

    serializeDocument(doc, outputDirectory.resolve("sec-roles.xml"));
  }

  private static void writeSecActions(
    final Path outputDirectory)
    throws Exception
  {
    final var db =
      DOCUMENTS.newDocumentBuilder();
    final var doc =
      db.newDocument();
    final var root =
      doc.createElementNS(STRUCTURAL_8, "Table");

    root.setAttribute("type", "genericTable");
    doc.appendChild(root);

    final var cols = doc.createElementNS(STRUCTURAL_8, "Columns");
    root.appendChild(cols);

    final var col0 = doc.createElementNS(STRUCTURAL_8,"Column");
    col0.setTextContent("Name");
    cols.appendChild(col0);

    final var col1 = doc.createElementNS(STRUCTURAL_8,"Column");
    col1.setTextContent("Description");
    cols.appendChild(col1);

    for (final var f : NPSecAction.class.getFields()) {
      final var row = doc.createElementNS(STRUCTURAL_8,"Row");
      root.appendChild(row);

      final var c0 = doc.createElementNS(STRUCTURAL_8,"Cell");
      row.appendChild(c0);

      final var t = doc.createElementNS(STRUCTURAL_8,"Term");
      t.setAttribute("type", "expression");

      final MActionName name =
        (MActionName) f.getDeclaringClass()
          .getMethod("action")
          .invoke(f.get(null));

      t.setTextContent(name.value().toString());
      c0.appendChild(t);

      final var c1 = doc.createElementNS(STRUCTURAL_8,"Cell");
      row.appendChild(c1);

      c1.setTextContent(
        f.getAnnotation(NPDocumentation.class).value()
      );
    }

    serializeDocument(doc, outputDirectory.resolve("sec-actions.xml"));
  }
}
