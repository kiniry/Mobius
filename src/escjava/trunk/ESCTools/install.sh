#!/bin/bash

# Check that the ESCTools directory exists and is in a fresh state.

# cd to the proper location above ESCTools.

# Unpack the toplevel so we have a directory structure.
tar xjf ESCTools-2.0a0-10-08-03-TopLevel.tbz

# cd into the ESCTools directory.
cd ESCTools

# Apply each patch.
bzcat ~/ESCTools-2.0a0-09-08-03-Calvin.patch.bz | patch -Np1
bzcat ~/ESCTools-2.0a0-09-08-03-Escjava.patch.bz | patch -Np1
bzcat ~/ESCTools-2.0a0-09-08-03-Houdini.patch.bz | patch -Np1
bzcat ~/ESCTools-2.0a0-09-08-03-Javafe.patch.bz | patch -Np1
bzcat ~/ESCTools-2.0a0-09-08-03-Rcc.patch.bz | patch -Np1
bzcat ~/ESCTools-2.0a0-09-08-03-Simplify.patch.bz | patch -Np1

# Unpack the zero-length files.
tar xjf ESCTools-2.0a0-09-08-03-ZeroLengthFiles.tbz

# Have the user create their own Makefile.local.

# Wait for them to finish.

# Clean, build, and test the release.
make clean build test



