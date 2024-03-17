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


package com.io7m.northpike.tools.maven.internal;

import com.io7m.jdownload.core.JDownloadErrorType;
import com.io7m.jdownload.core.JDownloadRequestType;
import com.io7m.jdownload.core.JDownloadRequests;
import com.io7m.jdownload.core.JDownloadSucceeded;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.strings.NPStringConstantApplied;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tools.api.NPToolEventType;
import com.io7m.northpike.tools.api.NPToolException;
import com.io7m.northpike.tools.api.NPToolFactoryType;
import com.io7m.northpike.tools.api.NPToolProcessOutput;
import com.io7m.northpike.tools.api.NPToolProgramResult;
import com.io7m.northpike.tools.api.NPToolTaskCompletedFailure;
import com.io7m.northpike.tools.api.NPToolTaskCompletedSuccessfully;
import com.io7m.northpike.tools.api.NPToolTaskInProgress;
import com.io7m.northpike.tools.api.NPToolTaskStarted;
import com.io7m.northpike.tools.api.NPToolType;
import com.io7m.northpike.tools.common.NPToolArchives;
import com.io7m.northpike.tools.common.NPToolExceptions;
import com.io7m.northpike.tools.common.NPToolExecutions;
import com.io7m.northpike.tools.common.NPToolHTTPClients;
import com.io7m.northpike.tools.common.NPToolResources;
import com.io7m.northpike.tools.maven.NPTMFactory3;
import com.io7m.streamtime.core.STTransferStatistics;
import com.io7m.verona.core.Version;
import org.apache.commons.lang3.SystemUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.net.URI;
import java.net.URISyntaxException;
import java.net.http.HttpClient;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.UUID;
import java.util.concurrent.Flow;
import java.util.concurrent.SubmissionPublisher;

import static com.io7m.northpike.strings.NPStringConstants.DOWNLOADING;
import static com.io7m.northpike.tools.common.NPToolExceptions.errorOfDownloadError;

/**
 * A Maven 3.* tool.
 */

public final class NPTM3 implements NPToolType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPTM3.class);

  private static final String DEFAULT_HOST =
    "repo1.maven.org";

  private static final String BINARIES_URL =
    "%s://%s/maven2/org/apache/maven/apache-maven/%s/apache-maven-%s-bin.tar.gz";
  private static final String BINARIES_CHECKSUM_URL =
    "%s://%s/maven2/org/apache/maven/apache-maven/%s/apache-maven-%s-bin.tar.gz.sha512";

  private static final String DIRECTORY_NAME =
    "apache-maven-%s";
  private static final String ARCHIVE_FILE_NAME =
    "apache-maven-%s-bin.tar.gz";
  private static final String ARCHIVE_FILE_TMP_NAME =
    "apache-maven-%s-bin.tar.gz";
  private static final String CHECKSUM_FILE_NAME =
    "apache-maven-%s-bin.tar.gz.sha512";
  private static final String CHECKSUM_FILE_TMP_NAME =
    "apache-maven-%s-bin.tar.gz.sha512.tmp";


  private final SubmissionPublisher<NPToolEventType> events;
  private final NPTMFactory3 factory;
  private final NPStrings strings;
  private final Version version;
  private final Path directory;
  private final CloseableCollectionType<NPToolException> resources;
  private final NPToolArchives archives;
  private String downloadHost = DEFAULT_HOST;
  private UUID taskId;
  private boolean https;

  /**
   * A Maven 3.* tool.
   *
   * @param inFactory   The factory
   * @param inStrings   The string resources
   * @param inVersion   The version
   * @param inDirectory The installation directory
   */

  public NPTM3(
    final NPTMFactory3 inFactory,
    final NPStrings inStrings,
    final Version inVersion,
    final Path inDirectory)
  {
    this.factory =
      Objects.requireNonNull(inFactory, "factory");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.version =
      Objects.requireNonNull(inVersion, "version");
    this.directory =
      Objects.requireNonNull(inDirectory, "directory");
    this.events =
      new SubmissionPublisher<>();
    this.resources =
      NPToolResources.createResourceCollection(inStrings);
    this.taskId =
      UUID.randomUUID();
    this.https =
      true;
    this.archives =
      new NPToolArchives(this.strings);
  }

  @Override
  public String toString()
  {
    return String.format("[Tool org.apache.maven %s]", this.version);
  }

  @Override
  public NPToolFactoryType factory()
  {
    return this.factory;
  }

  @Override
  public Flow.Publisher<NPToolEventType> events()
  {
    return this.events;
  }

  @Override
  public void install()
    throws InterruptedException, NPToolException
  {
    if (!this.isInstalled()) {
      this.downloadAndInstall();
    }
  }

  private void downloadAndInstall()
    throws InterruptedException, NPToolException
  {
    final var client =
      NPToolHTTPClients.create();

    final Path binaryFile;
    try {
      binaryFile = this.downloadBinary(client);
    } catch (final NPToolException e) {
      this.events.submit(new NPToolTaskCompletedFailure(this.taskId, e));
      throw e;
    }

    try {
      this.archives.unpackTarGZ(binaryFile, this.directory);
    } catch (final NPToolException e) {
      this.events.submit(new NPToolTaskCompletedFailure(this.taskId, e));
      throw e;
    }
  }

  private Path downloadBinary(
    final HttpClient client)
    throws NPToolException, InterruptedException
  {
    final var outputFile =
      this.directory.resolve(
        String.format(ARCHIVE_FILE_NAME, this.version));
    final var outputTmpFile =
      this.directory.resolve(
        String.format(ARCHIVE_FILE_TMP_NAME, this.version));

    final var checksumFile =
      this.directory.resolve(
        String.format(CHECKSUM_FILE_NAME, this.version));
    final var checksumTmpFile =
      this.directory.resolve(
        String.format(CHECKSUM_FILE_TMP_NAME, this.version));

    final var fileTarget =
      String.format(
        BINARIES_URL,
        this.https ? "https" : "http",
        this.downloadHost(),
        this.version,
        this.version
      );

    final var checksumTarget =
      String.format(
        BINARIES_CHECKSUM_URL,
        this.https ? "https" : "http",
        this.downloadHost(),
        this.version,
        this.version
      );

    LOG.debug("Download {}", fileTarget);
    LOG.debug("Checksum {}", checksumTarget);

    this.createTask(NPStringConstantApplied.applied(DOWNLOADING, fileTarget));

    final JDownloadRequestType request;
    try {
      request = JDownloadRequests.builder(
          client,
          new URI(fileTarget),
          outputFile,
          outputTmpFile
        )
        .setRequestModifier(NPToolHTTPClients::setUserAgent)
        .setChecksumRequestModifier(NPToolHTTPClients::setUserAgent)
        .setTransferStatisticsReceiver(this::onTaskInProgress)
        .setChecksumFromURL(
          new URI(checksumTarget),
          "SHA-512",
          checksumFile,
          checksumTmpFile,
          this::onTaskInProgress
        ).build();
    } catch (final URISyntaxException e) {
      throw NPToolExceptions.errorURI(this.strings, BINARIES_URL, e);
    }

    final var result = request.execute();
    if (result instanceof final JDownloadSucceeded success) {
      this.events.submit(new NPToolTaskCompletedSuccessfully(this.taskId));
      return success.outputFile();
    }
    throw errorOfDownloadError(this.strings, (JDownloadErrorType) result);
  }

  private void onTaskInProgress(
    final STTransferStatistics stats)
  {
    this.events.submit(
      new NPToolTaskInProgress(
        this.taskId,
        stats.percentNormalized().orElse(0.0))
    );
  }

  private void createTask(
    final NPStringConstantType name)
  {
    this.taskId = UUID.randomUUID();
    this.events.submit(new NPToolTaskStarted(this.taskId, name));
  }

  @Override
  public boolean isInstalled()
  {
    return Files.isExecutable(this.mvnExecutable());
  }

  private Path mvnExecutable()
  {
    final var formattedDirectoryName =
      String.format(DIRECTORY_NAME, this.version.toString());
    final var mvnBaseDir =
      this.directory.resolve(formattedDirectoryName);
    final var binDir =
      mvnBaseDir.resolve("bin");

    final Path mvnFile;
    if (SystemUtils.IS_OS_WINDOWS) {
      mvnFile = binDir.resolve("mvn.cmd");
    } else {
      mvnFile = binDir.resolve("mvn");
    }

    return mvnFile.toAbsolutePath().normalize();
  }

  @Override
  public void setHTTPs(
    final boolean b)
  {
    this.https = b;
  }

  @Override
  public NPToolProgramResult execute(
    final Path executionDirectory,
    final Map<String, String> environment,
    final List<String> arguments)
    throws NPToolException, InterruptedException
  {
    Objects.requireNonNull(executionDirectory, "executionDirectory");
    Objects.requireNonNull(environment, "environment");
    Objects.requireNonNull(arguments, "arguments");

    final var execution = new ArrayList<String>();
    execution.add(this.mvnExecutable().toString());
    execution.addAll(arguments);

    return NPToolExecutions.execute(
      LOG,
      this.strings,
      executionDirectory,
      environment,
      execution,
      (processName, processId, text) -> {
        this.events.submit(
          new NPToolProcessOutput(processName, processId, text)
        );
      }
    );
  }

  @Override
  public void setDownloadHost(
    final String host)
  {
    this.downloadHost = Objects.requireNonNull(host, "host");
  }

  @Override
  public String downloadHost()
  {
    return this.downloadHost;
  }

  @Override
  public void close()
    throws NPToolException
  {
    this.resources.close();
  }
}
