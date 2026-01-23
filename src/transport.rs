use std::fmt;
use std::str::FromStr;
use thiserror::Error;

/// Errors that can occur when parsing a transport from a string.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TransportConversionError {
    #[error("Invalid transport: {0}")]
    InvalidTransport(Box<str>),
    #[error("Missing ':' in imgref")]
    MissingColon,
}

/// Errors that can occur when parsing an image reference from a string.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ImageReferenceError {
    #[error("Unknown transport '{0}'")]
    InvalidTransport(Box<str>),
    #[error("Missing ':' in {0}")]
    MissingColon(Box<str>),
    #[error("Invalid empty name in {0}")]
    EmptyName(Box<str>),
    #[error("Missing // in docker:// in {0}")]
    MissingDockerSlashes(Box<str>),
}

/// A backend/transport for OCI/Docker images.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
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

/// Combination of a transport and image name.
///
/// For example, `docker://quay.io/exampleos/blah:latest` would be parsed as:
/// - transport: `Registry`
/// - name: `quay.io/exampleos/blah:latest`
///
/// # Name formats by transport
///
/// The `name` field format varies by transport:
///
/// | Transport | Name format | Example |
/// |-----------|-------------|---------|
/// | `Registry` | `[domain/]name[:tag][@digest]` | `quay.io/example/image:latest` |
/// | `OciDir` | `path[:reference]` | `/path/to/oci-layout:mytag` |
/// | `OciArchive` | `path[:reference]` | `/path/to/image.tar:v1.0` |
/// | `DockerArchive` | `path[:docker-reference]` | `/path/to/image.tar:myimage:tag` |
/// | `ContainerStorage` | `[[storage-spec]]{image-id\|docker-ref}` | `localhost/myimage:latest` |
/// | `Dir` | `path` | `/path/to/directory` |
/// | `DockerDaemon` | `docker-reference` or `algo:digest` | `myimage:latest` |
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ImageReference {
    /// The storage and transport for the image
    pub transport: Transport,
    /// The image name - format depends on transport (see struct docs)
    pub name: String,
}

impl ImageReference {
    /// Create a new image reference from a transport and name.
    ///
    /// # Examples
    /// ```
    /// use containers_image_proxy::{ImageReference, Transport};
    ///
    /// let imgref = ImageReference::new(Transport::Registry, "quay.io/example/image:tag");
    /// assert_eq!(imgref.to_string(), "docker://quay.io/example/image:tag");
    /// ```
    pub fn new(transport: Transport, name: impl Into<String>) -> Self {
        Self {
            transport,
            name: name.into(),
        }
    }

    /// Create a new registry image reference from a parsed OCI Reference.
    ///
    /// # Examples
    /// ```
    /// use containers_image_proxy::ImageReference;
    /// use oci_spec::distribution::Reference;
    ///
    /// let oci_ref: Reference = "quay.io/example/image:latest".parse().unwrap();
    /// let imgref = ImageReference::new_registry(oci_ref);
    /// assert_eq!(imgref.to_string(), "docker://quay.io/example/image:latest");
    /// ```
    pub fn new_registry(reference: oci_spec::distribution::Reference) -> Self {
        Self {
            transport: Transport::Registry,
            name: reference.whole(),
        }
    }

    /// Try to create a new registry image reference by parsing the name.
    ///
    /// Returns an error if the name is not a valid OCI distribution reference.
    ///
    /// # Examples
    /// ```
    /// use containers_image_proxy::ImageReference;
    ///
    /// let imgref = ImageReference::try_new_registry("quay.io/example/image:latest").unwrap();
    /// assert_eq!(imgref.to_string(), "docker://quay.io/example/image:latest");
    ///
    /// // Invalid references return an error
    /// assert!(ImageReference::try_new_registry("not a valid reference!").is_err());
    /// ```
    pub fn try_new_registry(name: &str) -> Result<Self, oci_spec::distribution::ParseError> {
        let reference: oci_spec::distribution::Reference = name.parse()?;
        Ok(Self::new_registry(reference))
    }

    /// For Registry transport, parse the name as an OCI distribution Reference.
    ///
    /// Returns `None` for non-Registry transports. For Registry transport,
    /// returns `Some(Result)` with the parsed reference or a parse error.
    ///
    /// This is useful when you need structured access to the registry, repository,
    /// tag, and digest components of a registry image reference.
    ///
    /// # Examples
    /// ```
    /// use containers_image_proxy::{ImageReference, Transport};
    ///
    /// let imgref: ImageReference = "docker://quay.io/example/image:latest".try_into().unwrap();
    /// let oci_ref = imgref.as_registry().unwrap().unwrap();
    /// assert_eq!(oci_ref.registry(), "quay.io");
    /// assert_eq!(oci_ref.repository(), "example/image");
    /// assert_eq!(oci_ref.tag(), Some("latest"));
    ///
    /// // Non-registry transports return None
    /// let imgref: ImageReference = "oci:/path/to/image".try_into().unwrap();
    /// assert!(imgref.as_registry().is_none());
    /// ```
    pub fn as_registry(
        &self,
    ) -> Option<Result<oci_spec::distribution::Reference, oci_spec::distribution::ParseError>> {
        if self.transport == Transport::Registry {
            Some(self.name.parse())
        } else {
            None
        }
    }

    /// For ContainerStorage transport, parse into structured components.
    ///
    /// Returns `None` for non-ContainerStorage transports.
    ///
    /// # Examples
    /// ```
    /// use containers_image_proxy::{ImageReference, Transport};
    ///
    /// // Simple image reference
    /// let imgref: ImageReference = "containers-storage:localhost/myimage:tag".try_into().unwrap();
    /// let csref = imgref.as_containers_storage().unwrap();
    /// assert_eq!(csref.store_spec(), None);
    /// assert_eq!(csref.image(), "localhost/myimage:tag");
    ///
    /// // With store specifier
    /// let imgref: ImageReference = "containers-storage:[overlay@/var/lib/containers]busybox".try_into().unwrap();
    /// let csref = imgref.as_containers_storage().unwrap();
    /// assert_eq!(csref.store_spec(), Some("overlay@/var/lib/containers"));
    /// assert_eq!(csref.image(), "busybox");
    ///
    /// // Normalizing sha256: prefix (workaround for skopeo#2750)
    /// let imgref: ImageReference = "containers-storage:sha256:abc123".try_into().unwrap();
    /// let csref = imgref.as_containers_storage().unwrap();
    /// assert_eq!(csref.image_for_skopeo(), "abc123");
    /// ```
    pub fn as_containers_storage(&self) -> Option<ContainersStorageRef<'_>> {
        if self.transport == Transport::ContainerStorage {
            Some(ContainersStorageRef::new(&self.name))
        } else {
            None
        }
    }
}

/// A parsed containers-storage reference.
///
/// The containers-storage transport has a complex format:
/// `containers-storage:[store-spec]image-ref`
///
/// Where:
/// - `store-spec` is optional: `[driver@graphroot+runroot:options]`
/// - `image-ref` can be: `@image-id`, `docker-ref`, or `docker-ref@image-id`
///
/// This struct provides access to the parsed components.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContainersStorageRef<'a> {
    store_spec: Option<&'a str>,
    image: &'a str,
}

impl<'a> ContainersStorageRef<'a> {
    fn new(name: &'a str) -> Self {
        // Check for store specifier: [...]
        if let Some(rest) = name.strip_prefix('[') {
            if let Some(bracket_end) = rest.find(']') {
                return Self {
                    store_spec: Some(&rest[..bracket_end]),
                    image: &rest[bracket_end + 1..],
                };
            }
        }
        Self {
            store_spec: None,
            image: name,
        }
    }

    /// The store specifier content (without brackets), if present.
    ///
    /// Format: `driver@graphroot+runroot:options` (all parts optional except graphroot)
    pub fn store_spec(&self) -> Option<&'a str> {
        self.store_spec
    }

    /// The image reference portion after any store specifier.
    pub fn image(&self) -> &'a str {
        self.image
    }

    /// Returns the image reference normalized for skopeo.
    ///
    /// This strips the `sha256:` prefix if present, working around
    /// [skopeo#2750](https://github.com/containers/skopeo/issues/2750) where
    /// skopeo expects bare image IDs without the algorithm prefix.
    pub fn image_for_skopeo(&self) -> &'a str {
        self.image.strip_prefix("sha256:").unwrap_or(self.image)
    }

    /// Convert back to an ImageReference, optionally applying skopeo normalization.
    ///
    /// If `normalize` is true, applies the sha256: stripping workaround.
    pub fn to_image_reference(&self, normalize: bool) -> ImageReference {
        let image = if normalize {
            self.image_for_skopeo()
        } else {
            self.image
        };

        let name = match self.store_spec {
            Some(spec) => format!("[{}]{}", spec, image),
            None => image.to_string(),
        };

        ImageReference::new(Transport::ContainerStorage, name)
    }
}

impl TryFrom<&str> for ImageReference {
    type Error = ImageReferenceError;

    /// Parse an image reference string into transport and name components.
    ///
    /// # Examples
    /// ```
    /// use containers_image_proxy::transport::{ImageReference, Transport};
    ///
    /// let imgref: ImageReference = "docker://quay.io/example/image:tag".try_into().unwrap();
    /// assert_eq!(imgref.transport, Transport::Registry);
    /// assert_eq!(imgref.name, "quay.io/example/image:tag");
    ///
    /// let imgref: ImageReference = "containers-storage:localhost/myimage".try_into().unwrap();
    /// assert_eq!(imgref.transport, Transport::ContainerStorage);
    /// assert_eq!(imgref.name, "localhost/myimage");
    /// ```
    fn try_from(value: &str) -> Result<Self, ImageReferenceError> {
        let (transport_name, mut name) = value
            .split_once(':')
            .ok_or_else(|| ImageReferenceError::MissingColon(value.into()))?;

        let transport = match transport_name {
            "registry" | "docker" => Transport::Registry,
            "oci" => Transport::OciDir,
            "oci-archive" => Transport::OciArchive,
            "docker-archive" => Transport::DockerArchive,
            "containers-storage" => Transport::ContainerStorage,
            "dir" => Transport::Dir,
            "docker-daemon" => Transport::DockerDaemon,
            prefix => {
                return Err(ImageReferenceError::InvalidTransport(prefix.into()));
            }
        };

        // Handle docker:// format - requires the // prefix
        if transport_name == "docker" {
            name = name
                .strip_prefix("//")
                .ok_or_else(|| ImageReferenceError::MissingDockerSlashes(value.into()))?;
        }

        if name.is_empty() {
            return Err(ImageReferenceError::EmptyName(value.into()));
        }

        Ok(Self {
            transport,
            name: name.to_string(),
        })
    }
}

impl FromStr for ImageReference {
    type Err = ImageReferenceError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl fmt::Display for ImageReference {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.transport, self.name)
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
        assert_eq!(err.to_string(), "Invalid transport: unknown");

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

    #[test]
    fn test_imagereference() {
        // Table of valid image references: (input, expected_transport, expected_name)
        let valid_cases: &[(&str, Transport, &str)] = &[
            ("oci:somedir", Transport::OciDir, "somedir"),
            ("dir:/some/dir/blah", Transport::Dir, "/some/dir/blah"),
            (
                "oci-archive:/path/to/foo.ociarchive",
                Transport::OciArchive,
                "/path/to/foo.ociarchive",
            ),
            (
                "docker-archive:/path/to/foo.dockerarchive",
                Transport::DockerArchive,
                "/path/to/foo.dockerarchive",
            ),
            (
                "containers-storage:localhost/someimage:blah",
                Transport::ContainerStorage,
                "localhost/someimage:blah",
            ),
            (
                "docker://quay.io/exampleos/blah:tag",
                Transport::Registry,
                "quay.io/exampleos/blah:tag",
            ),
            (
                "docker-daemon:myimage:latest",
                Transport::DockerDaemon,
                "myimage:latest",
            ),
            // registry: is asymmetric - parses but serializes as docker://
            (
                "registry:quay.io/exampleos/blah",
                Transport::Registry,
                "quay.io/exampleos/blah",
            ),
        ];

        for (input, expected_transport, expected_name) in valid_cases {
            let ir: ImageReference = (*input).try_into().unwrap();
            assert_eq!(ir.transport, *expected_transport, "transport for {input}");
            assert_eq!(ir.name, *expected_name, "name for {input}");
        }

        // Invalid image references
        let invalid_cases: &[&str] = &[
            "",            // empty
            "foo://bar",   // unknown transport
            "docker:blah", // docker without //
            "registry:",   // empty name
            "docker://",   // empty name after stripping //
            "foo:bar",     // unknown transport
            "nocolon",     // no colon at all
        ];

        for input in invalid_cases {
            assert!(
                ImageReference::try_from(*input).is_err(),
                "should fail: {input}"
            );
        }
    }

    #[test]
    fn test_imagereference_roundtrip() {
        // These should roundtrip exactly
        let roundtrip_cases: &[&str] = &[
            "oci:somedir",
            "oci-archive:/path/to/archive.tar",
            "docker-archive:/path/to/archive.tar",
            "containers-storage:localhost/myimage",
            "dir:/path/to/dir",
            "docker-daemon:myimage:latest",
            "docker://quay.io/example/image",
        ];

        for input in roundtrip_cases {
            let ir: ImageReference = (*input).try_into().unwrap();
            assert_eq!(*input, ir.to_string(), "roundtrip for {input}");
        }

        // registry: is asymmetric - serializes as docker://
        let ir: ImageReference = "registry:quay.io/example".try_into().unwrap();
        assert_eq!(ir.to_string(), "docker://quay.io/example");
    }

    #[test]
    fn test_imagereference_errors() {
        assert!(matches!(
            ImageReference::try_from("no-colon"),
            Err(ImageReferenceError::MissingColon(_))
        ));
        assert!(matches!(
            ImageReference::try_from("registry:"),
            Err(ImageReferenceError::EmptyName(_))
        ));
        assert!(matches!(
            ImageReference::try_from("docker://"),
            Err(ImageReferenceError::EmptyName(_))
        ));
        assert!(matches!(
            ImageReference::try_from("docker:blah"),
            Err(ImageReferenceError::MissingDockerSlashes(_))
        ));
        assert!(matches!(
            ImageReference::try_from("unknown:foo"),
            Err(ImageReferenceError::InvalidTransport(_))
        ));
    }

    #[test]
    fn test_imagereference_fromstr() {
        let ir1: ImageReference = "docker://quay.io/example/image".parse().unwrap();
        let ir2: ImageReference = "docker://quay.io/example/image".try_into().unwrap();
        assert_eq!(ir1, ir2);
    }

    #[test]
    fn test_containers_storage_ref() {
        // Table of test cases: (input, expected_store_spec, expected_image, expected_skopeo_image)
        let cases: &[(&str, Option<&str>, &str, &str)] = &[
            // Simple cases
            (
                "localhost/myimage:tag",
                None,
                "localhost/myimage:tag",
                "localhost/myimage:tag",
            ),
            ("busybox", None, "busybox", "busybox"),
            // With store specifier
            (
                "[overlay@/var/lib/containers]busybox",
                Some("overlay@/var/lib/containers"),
                "busybox",
                "busybox",
            ),
            (
                "[/var/lib/containers]busybox:tag",
                Some("/var/lib/containers"),
                "busybox:tag",
                "busybox:tag",
            ),
            (
                "[overlay@/var/lib/containers+/run/containers:opt1,opt2]image",
                Some("overlay@/var/lib/containers+/run/containers:opt1,opt2"),
                "image",
                "image",
            ),
            // sha256: prefix handling (skopeo#2750 workaround)
            (
                "sha256:abc123def456",
                None,
                "sha256:abc123def456",
                "abc123def456",
            ),
            (
                "[overlay@/tmp]sha256:abc123",
                Some("overlay@/tmp"),
                "sha256:abc123",
                "abc123",
            ),
            // Image ID without sha256: prefix (already normalized)
            ("abc123def456", None, "abc123def456", "abc123def456"),
            // Edge cases
            ("", None, "", ""),
            ("[]image", Some(""), "image", "image"),
        ];

        for (input, expected_store_spec, expected_image, expected_skopeo) in cases {
            let imgref = ImageReference::new(Transport::ContainerStorage, *input);
            let csref = imgref.as_containers_storage().unwrap();
            assert_eq!(
                csref.store_spec(),
                *expected_store_spec,
                "store_spec for {input}"
            );
            assert_eq!(csref.image(), *expected_image, "image for {input}");
            assert_eq!(
                csref.image_for_skopeo(),
                *expected_skopeo,
                "image_for_skopeo for {input}"
            );
        }

        // Non-containers-storage transport returns None
        let imgref: ImageReference = "docker://quay.io/example".try_into().unwrap();
        assert!(imgref.as_containers_storage().is_none());
    }

    #[test]
    fn test_containers_storage_ref_roundtrip() {
        let cases: &[(&str, bool, &str)] = &[
            // (input, normalize, expected_output)
            ("localhost/myimage:tag", false, "localhost/myimage:tag"),
            ("localhost/myimage:tag", true, "localhost/myimage:tag"),
            ("[overlay@/tmp]busybox", false, "[overlay@/tmp]busybox"),
            ("[overlay@/tmp]busybox", true, "[overlay@/tmp]busybox"),
            ("sha256:abc123", false, "sha256:abc123"),
            ("sha256:abc123", true, "abc123"), // normalized
            ("[store]sha256:abc123", false, "[store]sha256:abc123"),
            ("[store]sha256:abc123", true, "[store]abc123"), // normalized
        ];

        for (input, normalize, expected) in cases {
            let imgref = ImageReference::new(Transport::ContainerStorage, *input);
            let csref = imgref.as_containers_storage().unwrap();
            let result = csref.to_image_reference(*normalize);
            assert_eq!(
                result.name, *expected,
                "roundtrip for {input} normalize={normalize}"
            );
            assert_eq!(result.transport, Transport::ContainerStorage);
        }
    }
}
