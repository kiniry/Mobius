@echo off

rem Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
rem See LICENCE.TXT for details.


set BON_HOME=
set JAVA=java

set cp=%BON_HOME%/lib/BON.jar;%BON_HOME%/lib/antlr-2.7.7.jar;%BON_HOME%/lib/antlr-3.0.1.jar;%BON_HOME%/lib/CommandlineParser.jar;%BON_HOME%/lib/stringtemplate-3.1b1.jar

%JAVA% -cp %cp% ie.ucd.ebon.Main %*
