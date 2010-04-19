#!/bin/sh
cd parsing
ocamlyacc parser.mly
mv parser.mly /tmp
