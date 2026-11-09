FROM ubuntu:24.04
RUN apt-get update -qq && apt-get install -y -qq --no-install-recommends python3 python3-pip && \
    pip3 install --break-system-packages unicorn==2.1.1 && rm -rf /var/lib/apt/lists/*
