@echo off

rem To install ESC/Java2 on a new machine, change the following 
rem line to point to the directory containing the installation:
set ESCJAVA_ROOT=C:\cygwin\ESC\ESCTools




rem Some arguments to Simplify, passed via environment variables
set ESCJ_SIMPLIFY=%ESCJAVA_ROOT%\Simplify-1.5.4.exe
set ESCJ_SIMPLIFY_ARGS=-noprune -noplunge
set PROVER_KILL_TIME=300
set PROVER_CC_LIMIT=10

if "%ESCJ_STDARGS%"=="" set ESCJ_STDARGS=-nowarn Deadlock

rem ESCJ_ARGS is a variable local to this batch file
set ESCJ_ARGS=%*

rem USERPATH is a variable local to this batch file
if '%CLASSPATH%'=='' set USERPATH=.
if not '%CLASSPATH%'=='' set USERPATH=%CLASSPATH%
rem @echo on
rem echo %ESCJ_ARGS%
java  -Dsimplify="%ESCJ_SIMPLIFY%" -classpath "%ESCJAVA_ROOT%\esctools2.jar" escjava.Main -specs "%ESCJAVA_ROOT%\jmlspecs.jar" -classpath "%USERPATH%" %ESCJ_STDARGS% %ESCJ_ARGS%
