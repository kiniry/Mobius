@echo off

rem Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
rem See LICENCE.TXT for details.

rem You must set BON_HOME below. You can optionally set JAVA to use a specific version of java.

set BON_HOME=
set JAVA=java

if exist %BON_HOME%.\bonc.js (
  cscript /nologo %BON_HOME%.\bonc.js "%JAVA%" "%BON_HOME%" "%*"
) else (
  echo You must set BON_HOME in bonc.bat to be a valid location.
)
