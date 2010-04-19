#!/bin/sh
if [ -f parsing/parser.mly ]; then
  cd parsing
  ocamlyacc parser.mly
  mv parser.mly /tmp
fi
