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


package com.io7m.northpike.repository.jgit;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.repository.jgit.internal.NPSCMJGRepository;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryException;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryFactoryType;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryType;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.net.URI;
import java.nio.file.Path;
import java.util.Objects;

/**
 * JGit repository.
 */

public final class NPSCMRepositoriesJGit
  implements NPSCMRepositoryFactoryType
{
  private static final RDottedName NAME =
    new RDottedName("com.io7m.northpike.repository.jgit");

  private static final NPSCMProviderDescription PROVIDER =
    new NPSCMProviderDescription(
      NAME,
      "Eclipse JGit for Git repositories.",
      URI.create("https://eclipse.dev/jgit/")
    );

  /**
   * @return The provider
   */

  public static NPSCMProviderDescription providerGet()
  {
    return PROVIDER;
  }

  /**
   * JGit repository.
   */

  public NPSCMRepositoriesJGit()
  {

  }

  /**
   * @return The provider name
   */

  public static RDottedName providerNameGet()
  {
    return NAME;
  }

  @Override
  public NPSCMProviderDescription provider()
  {
    return PROVIDER;
  }

  @Override
  public RDottedName providerName()
  {
    return NAME;
  }

  @Override
  public NPSCMRepositoryType createRepository(
    final RPServiceDirectoryType services,
    final Path dataDirectory,
    final NPRepositoryDescription repository)
    throws NPSCMRepositoryException
  {
    Objects.requireNonNull(services, "services");
    Objects.requireNonNull(dataDirectory, "dataDirectory");
    Objects.requireNonNull(repository, "repository");

    return NPSCMJGRepository.create(services, dataDirectory, repository);
  }

  @Override
  public String description()
  {
    return "The JGit repository service.";
  }
}
