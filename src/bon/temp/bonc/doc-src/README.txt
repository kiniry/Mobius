Copyright (c) 2007, Fintan Fairmichael, University College Dublin
All rights reserved.

This file is the readme that accompanies the bonc tool.

Contents:

  1. Description
  2. Requirements
  3. Using the tool
  4. Source


1. DESCRIPTION
==============

  Bonc is a parser and typechecker for the Business Object Notation (BON).

  More information can be found on BON at the website 
  http://www.bon-method.com/, and by reading the book "Seamless object-oriented
  software architecture: analysis and design of reliable systems" which is 
  freely available on the site since it is out of print.


2. REQUIREMENTS
===============

  Since this tool has been written in Java, the only real requirements are a
  system that has a Java Runtime Environment (JRE) capable of running Java
  version 5 bytecode. The tool has been developed and tested primarily using
  Sun's official releases of Java, version 1.5/5.0 and 1.6/6.0. Whilst it might
  work with some of the alternative JRE implementations that support Java 5
  code, it has not been tested on these at all.

  The tool utilises the ANTLR parser generator, and releases of the tool
  include the appropriate ANTLR runtime as well as 

3. RUNNING THE TOOL
===================

  Note that in this section we assume that you have successfully completed an 
  installation procedure as described in INSTALLATION.txt. We will use the tool
  as if it is on the path (i.e. simply "bonc"), but you can substitute for 
  ./bonc, /path/to/bonc, or similar, if necessary.

  Firstly, to see the available options type:
    bonc --help

  Standard usage is:
    bonc [options] file1 [file2 ...]

  For example:
    bonc file1

  The tool will then parse and typecheck the input, and report any errors. If
  the tool does not output any messages, then no errors were found.

  You can read from standard input by adding the option "-" (single-dash). This
  can be given as a file, or an option. For example, the following three
  commands will all produce the same result:
    bonc - file1 file2
    bonc file1 - file2
    bonc file1 file2 -


4. SOURCE
=========

  All source for this tool is available from the subversion repository. The
  repository is located at: 
    https://mobius.ucd.ie/repos/src/bon/bonc

  You can browse the source in your web browser:
    https://mobius.ucd.ie/browser/src/bon

   For more information on how to download and build this software, please read
   INSTALLATION.txt.

