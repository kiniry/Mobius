#!/bin/sh

# Author: Paul Howarth
# http://forums.fedoraforum.org/showthread.php?t=42825 
 
# Run it from the top-level directly that you want to
# copy-by-linking, after setting the CHROOT value to the full pathname of
# the directory you want to create the copy in. This script will only link
# regular files, not symlinks, device files etc., but you should be able
# to modify it to do that fairly easily if you need to do that.


# TEMPLATE directory is root of tree you want to replicate.
# It should *not* be an absolute pathname.
TEMPLATE=.
CHROOT=$1

# CHROOT is absolute pathname of directory you want to clone the
# template to.
# It must be an absolute pathname and it must not be a subdirectory
# of the template directory.

# Replicate directory structure
find $TEMPLATE \! -wholename $CHROOT -and \! -name "*.svn*" -and -type d -exec mkdir -p $CHROOT/{} \;

# Make hard links to files
find $TEMPLATE \! -name "*.svn*" -and -type f -exec ln -f {} $CHROOT/{} \;
