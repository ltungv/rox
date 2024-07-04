#!/bin/bash

set -euxo

docker build -t rox-test .
docker run --rm rox-test
