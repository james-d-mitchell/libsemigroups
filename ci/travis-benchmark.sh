#!/bin/bash
set -e

# Setup
ci/travis-setup.sh

./configure
make bench_all -j4
# only compile don't run the benchmarks as they probably take too long.