FROM dart:2.19.6-sdk

RUN apt-get update \
    # Install build tools
    && apt-get install -y --no-install-recommends build-essential \
    && apt-get autoremove -y --purge \
    && apt-get autoclean \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/* \
    # Install rustup with the stable toolchain
    && curl --proto "=https" --tlsv1.2 -sSf https://sh.rustup.rs \
    | sh -s -- -y --default-toolchain stable --profile minimal \
    # Clone the test repository and get its dependencies
    && git clone https://github.com/munificent/craftinginterpreters.git \
    && cd craftinginterpreters \
    && make get

COPY . /root/rox
RUN chmod +x -R /root/rox/scripts
ENTRYPOINT ["/root/rox/scripts/entrypoint.sh"]
