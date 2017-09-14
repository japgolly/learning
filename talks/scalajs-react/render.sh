#!/bin/bash
cd "$(dirname "$(readlink -e "$0")")" || exit 1

t=src/.tmp.md
d=rendered
rm -rf $d $t

sed 's/fragment/aahhh/g' < src/scalajs-react.md > $t \
  && ../reveal-md $t -S $d \
  && cp src/{shipreq.svg,nim-crying.jpg,WHIRL.svg} $d/ \
  && rm -f $t

