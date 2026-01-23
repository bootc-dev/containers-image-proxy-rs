use std::fmt;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum TransportConversionError {
    #[error("Invalid transport")]
    InvalidTransport(Box<str>),
    #[error("Missing ':' in imgref")]
    MissingColon,
}

/// A backend/transport for OCI/Docker images.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Transport {
    /// A remote Docker/OCI registry (`registry:` or `docker://`)
    Registry,
    /// A local OCI directory (`oci:`)
    OciDir,
    /// A local OCI archive tarball (`oci-archive:`)
    OciArchive,
    /// A local Docker archive tarball (`docker-archive:`)
    DockerArchive,
    /// Local container storage (`containers-storage:`)
    ContainerStorage,
    /// Local directory (`dir:`)
    Dir,
    /// Local Docker daemon (`docker-daemon:`)
    DockerDaemon,
}

impl fmt::Display for Transport {
    /// Convert the transport back to its string representation.
    ///
    /// Note: Registry transport defaults to "docker://" format.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Transport::Registry => f.write_str("docker://"),
            Transport::OciDir => f.write_str("oci:"),
            Transport::OciArchive => f.write_str("oci-archive:"),
            Transport::DockerArchive => f.write_str("docker-archive:"),
            Transport::ContainerStorage => f.write_str("containers-storage:"),
            Transport::Dir => f.write_str("dir:"),
            Transport::DockerDaemon => f.write_str("docker-daemon:"),
        }
    }
}

impl TryFrom<&str> for Transport {
    type Error = TransportConversionError;

    /// Parse the transport type from a container image reference string, eg
    /// docker://quay.io/myimage, containers-storage:localhost/myimage
    ///
    /// Supports various transport types like "registry:", "oci:", "docker://", etc.
    /// Returns an error for unknown transports or malformed references without colons.
    fn try_from(imgref: &str) -> Result<Self, TransportConversionError> {
        if let Some(colon_pos) = imgref.find(':') {
            let transport_prefix = &imgref[..colon_pos];

            let transport = match transport_prefix {
                "registry" => Transport::Registry,
                "oci" => Transport::OciDir,
                "oci-archive" => Transport::OciArchive,
                "docker-archive" => Transport::DockerArchive,
                "containers-storage" => Transport::ContainerStorage,
                "dir" => Transport::Dir,
                "docker-daemon" => Transport::DockerDaemon,
                "docker" => {
                    // Check if this is actually "docker://" format
                    if imgref[colon_pos..].starts_with("://") {
                        Transport::Registry
                    } else {
                        return Err(TransportConversionError::InvalidTransport(
                            transport_prefix.into(),
                        ));
                    }
                }
                prefix => return Err(TransportConversionError::InvalidTransport(prefix.into())),
            };

            return Ok(transport);
        }

        Err(TransportConversionError::MissingColon)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transport_from_str() {
        // Test specific transports
        assert!(matches!(
            Transport::try_from("registry:example.com/image"),
            Ok(Transport::Registry)
        ));
        assert!(matches!(
            Transport::try_from("oci:/path/to/image"),
            Ok(Transport::OciDir)
        ));
        assert!(matches!(
            Transport::try_from("oci-archive:/path/to/archive.tar"),
            Ok(Transport::OciArchive)
        ));
        assert!(matches!(
            Transport::try_from("docker-archive:/path/to/archive.tar"),
            Ok(Transport::DockerArchive)
        ));
        assert!(matches!(
            Transport::try_from("containers-storage:example.com/image"),
            Ok(Transport::ContainerStorage)
        ));
        assert!(matches!(
            Transport::try_from("dir:/path/to/directory"),
            Ok(Transport::Dir)
        ));
        assert!(matches!(
            Transport::try_from("docker-daemon:example.com/image"),
            Ok(Transport::DockerDaemon)
        ));

        // Test docker:// prefix
        assert!(matches!(
            Transport::try_from("docker://example.com/image"),
            Ok(Transport::Registry)
        ));

        // Test bare image references with colon (port or tag)
        assert!(matches!(
            Transport::try_from("example.com:8080/image"),
            Err(TransportConversionError::InvalidTransport(_))
        ));
        assert!(matches!(
            Transport::try_from("example.com/image:tag"),
            Err(TransportConversionError::InvalidTransport(_))
        ));

        // Test unknown transport (should error)
        assert!(matches!(
            Transport::try_from("unknown:/path"),
            Err(TransportConversionError::InvalidTransport(_))
        ));
    }

    #[test]
    fn test_transport_error_cases() {
        // Test missing colon (bare image reference without transport)
        assert!(matches!(
            Transport::try_from("docker.io/library/hello-world"),
            Err(TransportConversionError::MissingColon)
        ));
        assert!(matches!(
            Transport::try_from("example.com/image"),
            Err(TransportConversionError::MissingColon)
        ));

        // Test invalid transport prefixes
        assert!(matches!(
            Transport::try_from("invalid:example.com/image"),
            Err(TransportConversionError::InvalidTransport(_))
        ));
        assert!(matches!(
            Transport::try_from("ftp:example.com/image"),
            Err(TransportConversionError::InvalidTransport(_))
        ));

        // Test docker: without :// (should error)
        assert!(matches!(
            Transport::try_from("docker:example.com/image"),
            Err(TransportConversionError::InvalidTransport(_))
        ));

        // Test empty string
        assert!(matches!(
            Transport::try_from(""),
            Err(TransportConversionError::MissingColon)
        ));

        // Test just colon
        assert!(matches!(
            Transport::try_from(":"),
            Err(TransportConversionError::InvalidTransport(_))
        ));
    }

    #[test]
    fn test_transport_edge_cases() {
        // Test transport at end of string
        assert!(matches!(
            Transport::try_from("registry:"),
            Ok(Transport::Registry)
        ));
        assert!(matches!(Transport::try_from("oci:"), Ok(Transport::OciDir)));

        // Test docker:// with empty path
        assert!(matches!(
            Transport::try_from("docker://"),
            Ok(Transport::Registry)
        ));

        // Test multiple colons (should use first colon position)
        assert!(matches!(
            Transport::try_from("registry:example.com:8080/image"),
            Ok(Transport::Registry)
        ));
        assert!(matches!(
            Transport::try_from("oci:/path/with:colon/image"),
            Ok(Transport::OciDir)
        ));
    }

    #[test]
    fn test_error_display() {
        let err = TransportConversionError::InvalidTransport("unknown".into());
        assert_eq!(err.to_string(), "Invalid transport");

        let err = TransportConversionError::MissingColon;
        assert_eq!(err.to_string(), "Missing ':' in imgref");
    }

    #[test]
    fn test_transport_display() {
        // Test that each transport converts to its expected string representation
        assert_eq!(Transport::Registry.to_string(), "docker://");
        assert_eq!(Transport::OciDir.to_string(), "oci:");
        assert_eq!(Transport::OciArchive.to_string(), "oci-archive:");
        assert_eq!(Transport::DockerArchive.to_string(), "docker-archive:");
        assert_eq!(
            Transport::ContainerStorage.to_string(),
            "containers-storage:"
        );
        assert_eq!(Transport::Dir.to_string(), "dir:");
        assert_eq!(Transport::DockerDaemon.to_string(), "docker-daemon:");
    }

    #[test]
    fn test_transport_roundtrip() {
        // Test roundtrip conversion for transports that map back to themselves
        let transports = [
            Transport::OciDir,
            Transport::OciArchive,
            Transport::DockerArchive,
            Transport::ContainerStorage,
            Transport::Dir,
            Transport::DockerDaemon,
        ];

        for original_transport in transports {
            let transport_str = original_transport.to_string();
            let parsed = Transport::try_from(transport_str.as_str()).unwrap();
            assert_eq!(
                parsed, original_transport,
                "Failed roundtrip for {original_transport:?}"
            );
        }

        // Test special case for Registry (docker:// -> Registry)
        let registry_str = Transport::Registry.to_string();
        let parsed = Transport::try_from(registry_str.as_str()).unwrap();
        assert!(matches!(parsed, Transport::Registry));
    }
}
