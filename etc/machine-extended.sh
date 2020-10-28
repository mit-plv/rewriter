#!/bin/sh

# save a way to get the stderr
exec 3>&2

# output set -x stuff to stdout
exec 2>&1

# put all the commands in a subshell so we don't print true at the end
(
set -x

# redirect errors to stderr
lscpu 2>&3
uname -a 2>&3
lsb_release -a 2>&3
)
true # never fail
