Copyright 2001, Compaq Computer Corporation.

NOTE: Aside from this note, this is the original README file from the
source release from HP/Compaq.  It provides general background, but the
build procedure has been considerably altered, simplified, and automated.
Read the contents of README.first for details. - DRCok 7/1/2003

This is the README.txt file that accompanies the source release
of Javafe, Escjava, Rcc, Houdini, and Simplify.  This README.txt
file will refer to these collections of sources as "envelopes",
to avoid confusion with several other meanings of "packages".

Note that the sources are provided pretty much as they existed at
Compaq SRC in November 2001.  Surely, the envelopes contain some dead
code and other files that may not be up-to-date.  Some documentation
and readme files may be confusing, incomplete, or just entirely wrong.
The tools could be built at Compaq SRC under Tru64 Unix at the time of
this source release, but are likely to require tweaking before they
would build on other platforms.  Nevertheless, the hope is that the
sources will still be more useful in this state than they would have
been had they not been released at all.  Although Compaq does not
promise to support the sources, you may attempt to send questions to
escjava@research.compaq.com.

Here are some general descriptions of the envelopes and how to
build them.  If you use more than one envelope, it is assumed that
you install them as subdirectories of the same directory (for example,
you may copy them as ~/proj/Javafe, ~/proj/Escjava, etc.).

* Javafe

  This is the Java front end that ESC/Java and Rcc use.  In
  addition to parsing and type checking Java, it allows subclasses
  to extend Java with annotations, like those in ESC/Java.
  How to do this may be documented in various files.  You can
  also look at the code in the Escjava and Rcc envelopes
  (for example, Escjava/java/escjava/Main.java) to see how ESC/Java
  and Rcc build on top of Javafe.

  First, you need to change the JDKBINARIES variable in Javafe/setup
  to point to your local Java runtime library, typically a file called
  rt.jar.
  
  Then, to build Javafe at Compaq SRC, do:

    tru64>  cd Javafe
    tru64>  source setup
    tru64>  gnumake javafe zip

  Your mileage may vary elsewhere.  You will also want to run the
  Javafe regression tests:

    tru64>  cd Javafe
    tru64>  source setup
    tru64>  gnumake javafe runtest

  At Compaq SRC, this yields no errors; errors reported when trying
  this elsewhere could be indicative of build problems rather than
  problems in the Javafe source.

  The Javafe sources are annotated with ESC/Java annotations.  You
  can therefore use ESC/Java to find errors in any changes you make
  to Javafe.  To run ESC/Java on all of the Javafe sources, do:

    tru64>  cd Javafe
    tru64>  source setup
    tru64>  gnumake javafe esc

  The Javafe envelope also contains the sources for some other useful
  Java tools, see the Javafe/java/jtools directory.

* Escjava

  This is the envelope containing the ESC/Java extensions of Javafe.
  To build all of ESC/Java, you need to build the Javafe (see above),
  Escjava, and Simplify (see below) envelopes.  If you have no interest
  in modifying the theorem prover, Simplify, you can simply build
  Javafe and Escjava.

  To build Escjava at Compaq SRC, do:

    tru64>  cd Escjava
    tru64>  source setup
    tru64>  gnumake escjava zip

  Your mileage may vary elsewhere.  You will also want to run the
  Escjava regression tests:

    tru64>  cd Escjava
    tru64>  source setup
    tru64>  gnumake escjava runtest

  This will report some errors, if they occur, but you will also
  need to study the output manually to see if any of the numbered
  tests failed.  If a numbered test fails, the word "Failed" will
  appear on the line after the test number.  The regression test
  harness uses various Unix command-line tools, which may require
  some porting effort on non-Tru64 platforms; you probably do want
  to invest this effort.  If you add functionality to ESC/Java, you'll
  want to add appropriate regression tests; see the "rtestall" script
  and "alltests" file in the Escjava/java/escjava/test directory (note
  also that this is the main Escjava regression test directory,
  whereas Escjava/test only contains a few tests).

  If you add command-line switches, you'll want to document these
  in Escjava/java/escjava/escjava.mtex.  To convert this file into
  both the Unix man format and HTML format, use the "mtex" tool,
  which you can download from http://research.compaq.com/SRC/software.

  The Escjava/release directory contains the files going into a
  recent binary release of ESC/Java.  If you want to the larger set
  of .spec files that are available as an optional part of the binary
  release, you'll have to get them from there (because getting those
  files requires you to be a Licensee in good standing under the Sun
  Community Source License).  If you do this, or if you have your own
  directory of specification files, you may want to change the
  definition of JDKSPEC_ROOT in the Escjava/setup file.

  If you want to run ESC/Java with the predicate abstraction options
  to infer loop invariants, see the comments about jMocha in the
  Escjava/setup file.

  By the way, the Escjava/java/instrumenter directory contains some
  files that once were used in a source-to-source convertion of
  many ESC/Java annotations into run-time checks.  The code is probably
  out of date with respect to the other source and ESC/Java's current
  annotation language, but the sources may be a good starting point
  for an effort to do this.

* Rcc

  This envelope contains the Race Condition Checker for Java.
  Building it requires the Javafe envelope (see above).  At
  Compaq SRC, you would then build Rcc as follows:

    tru64>  cd Rcc
    tru64>  source setup
    tru64>  gnumake rcc

  Your mileage may vary elsewhere.  To run the regression test suite, do:

    tru64>  cd Rcc
    tru64>  source setup
    tru64>  gnumake rcc runtest

* Houdini

  This is an annotation assistant for ESC/Java.  Building it
  requires the Javafe (see above), Escjava (see above), and Simplify
  (see below) envelopes.  At Compaq SRC, you would then build Houdini
  as follows:

    tru64>  cd Houdini
    tru64>  source setup
    tru64>  gnumake houdini

  Your mileage may vary elsewhere.

  Note, the Escjava envelope contains some files in its subdirectories
  "java/escwizard" and "java/houdini".  The first of these is an
  old annotation assistant for ESC/Java, whose code is probably
  out of date with the rest of the sources, and you probably wouldn't
  want to run it anyway.  The second of these directories contains
  some sources that may possibly be used by the Houdini envelope,
  and probably also contains some files that may have the appearance
  of being "the" Houdini.  Don't be fooled by these directories;
  instead, start here in the Houdini envelope.

  The Houdini tool 

* Simplify

  This envelope contains the sources for the theorem prover Simplify,
  which is used by the ESC/Java and Houdini tools.  Simplify is written
  in Modula-3, so you need a Modula-3 building environment, which
  you can download from the net, for example from Compaq SRC.  The
  Simplify envelope contains 4 packages (1 or 2 of which may possibly
  be part of your Modula-3 installation already).  Simplify add
  these 4 packages to your Modula-3 environment and build them
  (using "m3build", if you use SRC Modula-3).

We're interested in hearing about your use of the sources and tools
described in this file.  You may also be interested in inquiring
about ways of incorporating extensions you have built into a possible
future release or update of the above and other sources.  Feel
free to communicate with researchers who developed these tools by
sending mail to escjava@research.compaq.com.
 
