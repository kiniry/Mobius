Run it from the top-level directly that you want to
copy-by-linking, after setting the CHROOT value to the full pathname of
the directory you want to create the copy in. This script will only link
regular files, not symlinks, device files etc., but you should be able
to modify it to do that fairly easily if you need to do that.

#!/bin/sh

# TEMPLATE directory is root of tree you want to replicate.
# It should *not* be an absolute pathname.
TEMPLATE=$1.
CHROOT=$2

# CHROOT is absolute pathname of directory you want to clone the
# template to.
# It must be an absolute pathname and it must not be a subdirectory
# of the template directory.
CHROOT=/path/to/chroot

# Replicate directory structure
find $TEMPLATE -type d -exec mkdir -p $CHROOT/{} \;

# Make hard links to files
find $TEMPLATE -type f -exec ln {} $CHROOT/{} \;
