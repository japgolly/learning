#!/bin/bash
cd "$(dirname "$(readlink -e "$0")")" || exit 1

d=rendered
rm -rf $d

../reveal-md src/scalajs-react.md -S $d \
  && cp src/{shipreq.svg,nim-crying.jpg,WHIRL.svg} $d/

