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


package com.io7m.northpike.agent.workexec.podman.internal;

import com.io7m.cedarbridge.runtime.api.CBProtocolMessageVersionedSerializerType;
import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.bssio.CBSerializationContextBSSIO;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.jbssio.api.BSSReaderSequentialType;
import com.io7m.jbssio.api.BSSWriterSequentialUnsupported;
import com.io7m.jbssio.vanilla.BSSReaders;
import com.io7m.jbssio.vanilla.BSSWriters;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.locks.NPAgentResourceLockServiceType;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutionType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.local.NPWEMessages;
import com.io7m.northpike.agent.workexec.local.cb.NWEOutput;
import com.io7m.northpike.agent.workexec.local.cb.ProtocolNWE;
import com.io7m.northpike.agent.workexec.local.cb.ProtocolNWEType;
import com.io7m.northpike.agent.workexec.local.cb.ProtocolNWEv1Type;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.protocol.agent.NPACommandSWorkSent;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.tavella.api.PodmanExecutableType;
import com.io7m.tavella.api.PodmanImage;
import com.io7m.tavella.api.PodmanTmpFSFlag;
import com.io7m.tavella.api.PodmanTmpFSMount;
import com.io7m.tavella.api.PodmanVolumeFlag;
import com.io7m.tavella.api.PodmanVolumeMount;
import com.io7m.tavella.api.PodmanVolumeMountSourceType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedReader;
import java.io.EOFException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.OffsetDateTime;
import java.util.HexFormat;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.Flow;
import java.util.concurrent.SubmissionPublisher;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;

import static com.io7m.northpike.agent.workexec.api.NPAWorkEvent.Severity.ERROR;
import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult.FAILURE;
import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult.SUCCESS;
import static com.io7m.northpike.strings.NPStringConstants.CONTAINER_IMAGE;
import static com.io7m.northpike.strings.NPStringConstants.CONTAINER_REGISTRY;
import static com.io7m.northpike.strings.NPStringConstants.CONTAINER_TAG;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_RESOURCE_CLOSING;
import static com.io7m.northpike.strings.NPStringConstants.PROGRAM;
import static java.nio.charset.StandardCharsets.UTF_8;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;
import static java.util.Map.entry;

final class NPWorkExecutionPodman implements NPAWorkExecutionType
{
  private static final OpenOption[] FILE_OPTIONS = {
    CREATE,
    TRUNCATE_EXISTING,
    WRITE,
  };

  private final AtomicBoolean closed;
  private final CloseableCollectionType<NPException> resources;
  private final NPAgentWorkItem workItem;
  private final NPStrings strings;
  private final Path tmpWorkItemFile;
  private final Path workVolumeHostPath;
  private final PodmanExecutableType podman;
  private final PodmanImage podmanImage;
  private final PodmanTmpFSMount tmpHomeVolume;
  private final PodmanTmpFSMount tmpRootVolume;
  private final PodmanTmpFSMount tmpTmpVolume;
  private final PodmanVolumeMount workExecVolume;
  private final PodmanVolumeMount workItemVolume;
  private final PodmanVolumeMount workVolume;
  private final SubmissionPublisher<NPAWorkEvent> events;
  private final NPAgentResourceLockServiceType locks;
  private final NPAgentLocalName agentName;
  private final AtomicLong eventIndex;
  private final Optional<String> podName;

  NPWorkExecutionPodman(
    final NPStrings inStrings,
    final NPAgentResourceLockServiceType inLocks,
    final NPAWorkExecutorConfiguration inConfiguration,
    final NPAgentLocalName inAgentName,
    final PodmanExecutableType inPodman,
    final PodmanImage inPodmanImage,
    final PodmanVolumeMount inWorkExecVolume,
    final Optional<String> inPodName,
    final NPAgentWorkItem inWorkItem)
  {
    Objects.requireNonNull(inConfiguration, "configuration");

    this.agentName =
      Objects.requireNonNull(inAgentName, "agentName");
    this.podman =
      Objects.requireNonNull(inPodman, "podman");
    this.podmanImage =
      Objects.requireNonNull(inPodmanImage, "podmanImage");
    this.workExecVolume =
      Objects.requireNonNull(inWorkExecVolume, "workExecVolume");
    this.workItem =
      Objects.requireNonNull(inWorkItem, "workItem");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.locks =
      Objects.requireNonNull(inLocks, "locks");
    this.podName =
      Objects.requireNonNull(inPodName, "podName");

    this.eventIndex =
      new AtomicLong(1L);

    this.tmpWorkItemFile =
      inConfiguration.temporaryDirectory()
        .resolve(workItemFileName(inWorkItem));

    this.workItemVolume =
      new PodmanVolumeMount(
        new PodmanVolumeMountSourceType.HostPath(this.tmpWorkItemFile),
        "/northpike-work-item.nwi",
        Set.of(
          PodmanVolumeFlag.READ_ONLY,
          PodmanVolumeFlag.NO_DEVICES,
          PodmanVolumeFlag.NO_EXECUTABLE,
          PodmanVolumeFlag.NO_SETUID,
          PodmanVolumeFlag.SELINUX_LABEL_PRIVATE
        )
      );

    this.tmpHomeVolume =
      new PodmanTmpFSMount(
        "/home",
        Optional.empty(),
        Set.of(
          PodmanTmpFSFlag.READ_WRITE,
          PodmanTmpFSFlag.NO_DEVICES,
          PodmanTmpFSFlag.NO_SETUID
        )
      );

    this.tmpRootVolume =
      new PodmanTmpFSMount(
        "/root",
        Optional.empty(),
        Set.of(
          PodmanTmpFSFlag.READ_WRITE,
          PodmanTmpFSFlag.NO_DEVICES,
          PodmanTmpFSFlag.NO_EXECUTABLE,
          PodmanTmpFSFlag.NO_SETUID
        )
      );

    final var containers =
      inConfiguration.workDirectory()
        .resolve("containers");

    this.workVolumeHostPath =
      containers.resolve(
        this.workItem.identifier()
          .assignmentExecutionId()
          .toString()
      );

    this.workVolume =
      new PodmanVolumeMount(
        new PodmanVolumeMountSourceType.HostPath(this.workVolumeHostPath),
        "/northpike/work",
        Set.of(
          PodmanVolumeFlag.READ_WRITE,
          PodmanVolumeFlag.NO_DEVICES,
          PodmanVolumeFlag.NO_SETUID,
          PodmanVolumeFlag.SELINUX_LABEL_PRIVATE
        )
      );

    this.tmpTmpVolume =
      new PodmanTmpFSMount(
        "/northpike/temporary",
        Optional.empty(),
        Set.of(
          PodmanTmpFSFlag.READ_WRITE,
          PodmanTmpFSFlag.NO_DEVICES,
          PodmanTmpFSFlag.NO_SETUID
        )
      );

    this.resources =
      CloseableCollection.create(() -> new NPException(
        inStrings.format(ERROR_RESOURCE_CLOSING),
        new NPErrorCode("resources"),
        Map.of(),
        Optional.empty()
      ));

    this.resources.add(() -> Files.deleteIfExists(this.tmpWorkItemFile));

    this.events =
      this.resources.add(new SubmissionPublisher<>());
    this.closed =
      new AtomicBoolean(false);
  }

  private long nextEventIndex()
  {
    return this.eventIndex.getAndIncrement();
  }

  private static String workItemHashName(
    final NPAgentWorkItem workItem)
  {
    try {
      final var id =
        workItem.identifier();
      final var digest =
        MessageDigest.getInstance("SHA-256");
      digest.update(id.assignmentExecutionId().toString().getBytes(UTF_8));
      digest.update(id.planElementName().toString().getBytes(UTF_8));
      return HexFormat.of().formatHex(digest.digest());
    } catch (final NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }

  private static String workItemFileName(
    final NPAgentWorkItem workItem)
  {
    return "%s.nwi".formatted(workItemHashName(workItem));
  }

  @Override
  public Flow.Publisher<NPAWorkEvent> events()
  {
    return this.events;
  }

  @Override
  public NPAWorkExecutionResult execute()
  {
    try {
      this.storeWorkItem();

      Files.createDirectories(this.workVolumeHostPath);

      final var runBuilder =
        this.podman.run()
          .setImage(this.podmanImage)
          .setRootReadOnly(true)
          .setRemoveAfterExit(true);

      this.podName.ifPresent(runBuilder::setPod);

      final var environment =
        this.workItem.toolExecution().environment();

      for (final var entry : environment.entrySet()) {
        runBuilder.addEnvironmentVariable(entry.getKey(), entry.getValue());
      }

      try (var ignored = this.locks.lockWithDefaultTimeout(
        this.agentName,
        this.workItem.lockResources()
      )) {
        final var process =
          runBuilder.addEnvironmentVariable(
              "NORTHPIKE_WORKEXEC_HOME",
              "/northpike-workexec")
            .addEnvironmentVariable("HOSTNAME", "northpike")
            .addVolume(this.workExecVolume)
            .addVolume(this.workVolume)
            .addVolume(this.workItemVolume)
            .addTmpFS(this.tmpRootVolume)
            .addTmpFS(this.tmpHomeVolume)
            .addTmpFS(this.tmpTmpVolume)
            .addArgument("/northpike-workexec/bin/northpike-workexec")
            .addArgument("execute")
            .addArgument("--agent")
            .addArgument(this.agentName.toString())
            .addArgument("--work-item")
            .addArgument(this.workItemVolume.containerPath())
            .addArgument("--work-directory")
            .addArgument(this.workVolume.containerPath())
            .addArgument("--temporary-directory")
            .addArgument(this.tmpTmpVolume.containerPath())
            .addArgument("--log-format")
            .addArgument("BINARY")
            .build()
            .start();

        this.resources.add(process::destroyForcibly);

        final var outThread =
          Thread.ofVirtual()
            .start(() -> this.transformOutputEvents(process.getInputStream()));

        final var errThread =
          Thread.ofVirtual()
            .start(() -> transformErrorEvents(process.getErrorStream()));

        process.waitFor();
        outThread.join();
        errThread.join();

        if (process.exitValue() != 0) {
          return FAILURE;
        }

        return SUCCESS;
      }
    } catch (final NPException e) {
      this.events.submit(new NPAWorkEvent(
        ERROR,
        OffsetDateTime.now(),
        this.nextEventIndex(),
        Objects.requireNonNullElse(
          e.getMessage(),
          e.getClass().getCanonicalName()
        ),
        e.attributes(),
        Optional.of(NPStoredException.ofException(e))
      ));
      return FAILURE;
    } catch (final Exception e) {
      this.events.submit(new NPAWorkEvent(
        ERROR,
        OffsetDateTime.now(),
        this.nextEventIndex(),
        Objects.requireNonNullElse(
          e.getMessage(),
          e.getClass().getCanonicalName()
        ),
        Map.ofEntries(
          entry(
            this.localize(PROGRAM),
            "/northpike-workexec/bin/northpike-workexec"),
          entry(
            this.localize(CONTAINER_IMAGE), this.podmanImage.imageName()),
          entry(
            this.localize(CONTAINER_TAG), this.podmanImage.imageTag()),
          entry(
            this.localize(CONTAINER_REGISTRY), this.podmanImage.registry())
        ),
        Optional.of(NPStoredException.ofException(e))
      ));
      return FAILURE;
    }
  }

  private void storeWorkItem()
    throws IOException, NPProtocolException
  {
    final var validator = new NPA1Messages();
    try (var output =
           Files.newOutputStream(this.tmpWorkItemFile, FILE_OPTIONS)) {
      final var context =
        CBSerializationContextBSSIO.createFromOutputStream(
          new BSSWriters(),
          output
        );

      CBUUID.serialize(
        context,
        new CBUUID(NPA1Messages.protocolId())
      );
      context.writeU32(1L);
      context.flush();

      validator.writeLengthPrefixed(
        output,
        new NPACommandSWorkSent(UUID.randomUUID(), this.workItem)
      );
      output.flush();
    }
  }

  private static final Logger LOG =
    LoggerFactory.getLogger(NPWorkExecutionPodman.class);

  private static void transformErrorEvents(
    final InputStream errorStream)
  {
    try (var streamReader = new InputStreamReader(errorStream, UTF_8)) {
      try (var reader = new BufferedReader(streamReader)) {
        while (true) {
          final var line = reader.readLine();
          if (line == null) {
            break;
          }
          LOG.info("{}", line);
        }
      }
    } catch (final IOException e) {
      LOG.error("Failed to read process error output: ", e);
    }
  }

  private static final BSSReaderProviderType READERS =
    new BSSReaders();
  private static final ProtocolNWE PROTOCOL =
    new ProtocolNWE();

  private void transformOutputEvents(
    final InputStream inputStream)
  {
    try {
      try (var reader =
             READERS.createReaderFromStream(
               URI.create("input"), inputStream, "main")) {

        final var magic = reader.readU32BE();
        if (magic != 0x4E505745L) {
          throw new IOException("Unexpected magic number.");
        }
        LOG.debug("Magic: 0x{}", Long.toUnsignedString(magic, 16));
        final var version = reader.readU32BE();
        LOG.debug("Version: {}", Long.toUnsignedString(version));

        final var inputDeserializer =
          PROTOCOL.serializerForProtocolVersion(version)
            .orElseThrow();

        this.transformOutputEventsLoop(reader, inputDeserializer);
      }
    } catch (final IOException e) {
      this.events.submit(new NPAWorkEvent(
        ERROR,
        OffsetDateTime.now(),
        this.nextEventIndex(),
        Objects.requireNonNullElse(
          e.getMessage(),
          e.getClass().getCanonicalName()
        ),
        Map.of(),
        Optional.of(NPStoredException.ofException(e))
      ));
    }
  }

  private void transformOutputEventsLoop(
    final BSSReaderSequentialType reader,
    final CBProtocolMessageVersionedSerializerType<ProtocolNWEType> inputDeserializer)
    throws IOException
  {
    while (true) {
      try {
        final var length = reader.readU32BE("Length");
        LOG.debug("Size {}", Long.valueOf(length));

        try (var dataReader =
               reader.createSubReaderBounded("Message", length)) {
          final var inputContext =
            CBSerializationContextBSSIO.create(
              dataReader,
              new BSSWriterSequentialUnsupported(),
              () -> {
                // Nothing
              }
            );

          this.events.submit(
            this.transformMessage(inputDeserializer.deserialize(inputContext))
          );
        }
      } catch (final EOFException e) {
        LOG.debug("EOF: ", e);
        return;
      }
    }
  }

  private NPAWorkEvent transformMessage(
    final ProtocolNWEType message)
  {
    return switch (message) {
      case final ProtocolNWEv1Type v1 -> {
        yield switch (v1) {
          case final NWEOutput out -> {
            yield this.transformOutputV1(out);
          }
        };
      }
    };
  }

  private NPAWorkEvent transformOutputV1(
    final NWEOutput out)
  {
    final var exception =
      out.fieldException()
        .asOptional()
        .map(NPWEMessages::exceptionOfWire);

    return new NPAWorkEvent(
      exception.map(e -> ERROR).orElse(NPAWorkEvent.Severity.INFO),
      out.fieldTimestamp().value(),
      this.nextEventIndex(),
      out.fieldOutput().value(),
      CBMaps.toMapString(out.fieldAttributes()),
      out.fieldException()
        .asOptional()
        .map(NPWEMessages::exceptionOfWire)
    );
  }

  private String localize(
    final NPStringConstantType c)
  {
    return this.strings.format(c);
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public void close()
    throws NPException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
    }
  }
}
