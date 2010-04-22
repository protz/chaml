#!/bin/sh
if [ -f /tmp/parser.mly ]; then
  mv /tmp/parser.mly parsing
  rm -f parsing/parser.ml parsing/parser.mli
fi
