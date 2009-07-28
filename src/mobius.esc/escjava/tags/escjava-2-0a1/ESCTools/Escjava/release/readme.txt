# Copyright 2000, 2001, Compaq Computer Corporation

Here are the instructions for building a new ESC/Java release.

0. Set the version number and date of the new release in
   Escjava/java/escjava/Main.java.  And set the version in
   in Escjava/release/buildit to the same version number.

1. If this ESC/Java release uses the same version of Simplify as the
   previous ESC/Java release, go to step 2.

   If there's an updated version of Simplify, add these new files
   to the Escjava/release/master/bin directory.  If X.Y.Z is the new
   version of Simplify, do:

   unix>  cd Escjava/release/master/bin
   unix>  cvs add -kb Simplify-X.Y.Z.tru64
   unix>  cvs add -kb Simplify-X.Y.Z.exe.win
   unix>  cvs add -kb Simplify-X.Y.Z.linux
   unix>  cvs add -kb Simplify-X.Y.Z.solaris
   unix>  cvs commit Simplify-X.Y.Z.*

   Then, update Escjava/release/buildit to contain the new Simplify
   version number.

   Finally, save the Simplify sources:

   unix>  tar cf simplify.src.tar /proj/m3/pkg/simplify/src
   unix>  tar cf prover.src.tar /proj/m3/pkg/prover/src
   unix>  tar cf digraph.src.tar /proj/m3/pkg/digraph/src
   unix>  compress simplify.src.tar
   unix>  compress prover.src.tar
   unix>  compress digraph.src.tar

   See step 10 below for what to do with the *.src.tar.Z files.

2. Update (using "cvs update") your Javafe, Escjava, and specs
   directories.

   unix>  cd Javafe
   unix>  cvs update -d | grep -v "?"
   unix>  cd Escjava
   unix>  cvs update -d | grep -v "?"
   unix>  cd specs
   unix>  cvs update -d | grep -v "?"

   Make sure all of your local files are up-to-date and are the
   ones also checked into CVS.

3. Build Javafe:

   unix>  cd Javafe
   unix>  source setup
   unix>  gnumake clean depend javafe zip

4. Build Escjava:

   unix>  cd Escjava
   unix>  source setup
   unix>  gnumake clean depend escjava zip

5. Build the man pages:

   unix>  cd Escjava/java/escjava
   unix>  gnumake doc

6. Build the release files:

   unix>  cd Escjava/release
   unix>  cleanit
   unix>  buildit

7. Make the Windows .zip files into self-extracting executables.
   If X.Y.Z is the new ESC/Java version number, open
   Escjava/release/release/escjava-X.Y.Z-win.zip in WinZip under Windows.
   Select Action-->Make .EXE File, and specify

     c:\Program Files\escjava

   as the default directory.  Then, open
   Escjava/release/release/escjava-specs-X.Y.Z-win.zip in WinZip.
   Select Action-->Make .EXE File, and specify

     c:\Program Files\escjava

   as the default directory.

8. Make copies of the sources and release files.

   unix>  mkdir temp-X.Y.Z
   unix>  cd temp-X.Y.Z
   unix>  cvs -d /src/escjava/CVS checkout Javafe
   unix>  cvs -d /src/escjava/CVS checkout Escjava
   unix>  cvs -d /src/escjava/CVS checkout specs
   unix>  tar cf Javafe.tar Javafe
   unix>  tar cf Escjava.tar Escjava
   unix>  tar cf specs.jar specs
   unix>  compress Javafe.tar
   unix>  compress Escjava.tar
   unix>  compress specs.jar
   -->  store Javafe.tar.Z, Escjava.tar.Z, and specs.jar.Z in a good
        place (see 10 below); then:
   unix>  cd ..
   unix>  rm -r temp-X.Y.Z

9. Point Drew Kramer <kramer@pa.dec.com> to the files:

   escjava-X.Y.Z-tru64.tar.Z
   escjava-X.Y.Z-linux.tar.Z
   escjava-X.Y.Z-solaris.tar.Z
   escjava-X.Y.Z-win.exe
   escjava-specs-X.Y.Z-unix.tar.Z
   escjava-specs-X.Y.Z-win.exe

   Ask Drew to add these to the Compaq+ESC+for+Java directory
   at the Compaq Research download site.  Remind him that
   the first four of these files should use the default binary
   license, whereas the last two (that is, the two files *-specs-*)
   use an amended license which also mentions the Sun Community
   Source License.

10. To install ESC/Java at SRC and store the snapshot of the sources
    captured in steps 1 and 8 above, see the README file in the
    cra/escjava package.  That is, do:

    unix>  cd pkg/cra/escjava

    where "pkg" is your local "pkg" directory, which usually lives
    in your home directory.  If you don't have this directory, create
    it and then do:  cd pkg/cra/escjava ; getpackage -i
    
    Follow the directions in the README file (but to avoid an infinite
    loop, ignore the step that says to follow the instructions in this
    Escjava/release/readme.txt file).

11. Kick back.  Wait for fan mail.
