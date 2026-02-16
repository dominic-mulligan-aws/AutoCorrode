#!/bin/bash
# Download AWS SDK v2 JARs for Bedrock Runtime

set -e

VERSION="2.41.21"
BASE_URL="https://repo1.maven.org/maven2/software/amazon/awssdk"
LIB_DIR="$(dirname "$0")/lib"

mkdir -p "$LIB_DIR"

JARS=(
    "bedrock"
    "bedrockruntime"
    "sdk-core"
    "aws-core"
    "regions"
    "auth"
    "http-client-spi"
    "json-utils"
    "protocol-core"
    "aws-json-protocol"
    "http-auth"
    "http-auth-aws"
    "apache-client"
    "url-connection-client"
    "profiles"
    "utils"
    "metrics-spi"
    "endpoints-spi"
    "annotations"
    "http-auth-spi"
    "identity-spi"
    "checksums"
    "checksums-spi"
    "third-party-jackson-core"
    "retries"
    "retries-spi"
)

# Additional third-party dependencies
THIRD_PARTY=(
    "org/slf4j/slf4j-api/1.7.36/slf4j-api-1.7.36.jar"
    "org/reactivestreams/reactive-streams/1.0.4/reactive-streams-1.0.4.jar"
    "com/samskivert/jmustache/1.16/jmustache-1.16.jar"
    "org/scilab/forge/jlatexmath/1.0.7/jlatexmath-1.0.7.jar"
    "org/scilab/forge/jlatexmath-font-greek/1.0.7/jlatexmath-font-greek-1.0.7.jar"
    "org/scilab/forge/jlatexmath-font-cyrillic/1.0.7/jlatexmath-font-cyrillic-1.0.7.jar"
)

echo "Downloading AWS SDK v2 JARs (version $VERSION)..."

for jar in "${JARS[@]}"; do
    url="${BASE_URL}/${jar}/${VERSION}/${jar}-${VERSION}.jar"
    dest="${LIB_DIR}/${jar}-${VERSION}.jar"
    if [ ! -f "$dest" ]; then
        echo "  Downloading $jar..."
        curl -sL "$url" -o "$dest"
    else
        echo "  $jar already exists"
    fi
done

echo "Downloading third-party dependencies..."
for path in "${THIRD_PARTY[@]}"; do
    filename=$(basename "$path")
    dest="${LIB_DIR}/${filename}"
    if [ ! -f "$dest" ]; then
        echo "  Downloading $filename..."
        curl -sL "https://repo1.maven.org/maven2/${path}" -o "$dest"
    fi
done

echo ""
echo "Done. JARs downloaded to $LIB_DIR"
echo ""
ls -lh "$LIB_DIR"/*.jar | awk '{print $9, $5}'
