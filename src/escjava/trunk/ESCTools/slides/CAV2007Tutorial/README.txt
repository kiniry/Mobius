This directory contains materials for the tutorial by Gary T. Leavens
(with help from Joseph R. Kiniry and Erik Poll) given at CAV 2007.

The time available for this was 3 hours, split into two 1.5 hour parts.
In the event, the tutorial ran just about in the right length of time,
but this depended on not taking too much time for the demos.

The main file is JMLTutorial.tex.

A starting point was the tutorial material in ../ETAPSTutorial/,
and the various talks and tutorial papers on JML.

See Objectives.txt for the goals of this tutorial.

The powerpoint files that are used to make the various pdf graphics
included are in new-diagrams.ppt.  They are printed individually to
the PDF files included in the talk, and this is done using a custom
page size of 6 inches (wide) by 10 inches (high), although on the
screen it looks like 10 inches wide by 6 high.

To get the handouts, you have to answer y to the question that comes
up when running pdflatex on JMLTutorial.tex starts, and you have to be
running pdflatex on a TeX install that has pgf installed.  (Miktex has
it, or can if you install it, and the Makefile assumes that mpdflatex
is the Miktex version of pdflatex.)

Examples are mainly kept in the subdirectory examples/.
The directory examples_toedit/ contains copies of some files to use
when starting examples that are to be edited.  This directories
contents should be copied into examples_worked before the start of the
show.


$Id$
