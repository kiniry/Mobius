@echo off

rem To install ESC/Java2 on a new machine, change the following two
rem lines appropriately:
set ESCJAVA_ROOT=F:\ESCJava-2.0a5
rem set JAVA=F:\jsdk\1.4.2\bin\Java.exe

set ESCJAVA_ROOT=C:/cygwin/ESC/ESCTools



rem Some arguments to Simplify, passed via environment variables
rem set ESCJ_SIMPLIFY=%ESCJAVA_ROOT%\bin\Simplify-1.5.4.exe
set ESCJ_SIMPLIFY=%ESCJAVA_ROOT%\Simplify-1.5.4.exe
set ESCJ_SIMPLIFY_ARGS=-noprune -noplunge
set PROVER_KILL_TIME=300
set PROVER_CC_LIMIT=10

if "%ESCJ_STDARGS%"=="" set ESCJ_STDARGS=-nowarn Deadlock

rem ESCJ_ARGS is a variable local to this batch file
set ESCJ_ARGS=%*
rem :getargs
rem shift
rem if "%1"=="" goto endGetargs
rem set ESCJ_ARGS=%ESCJ_ARGS% %1
rem goto getargs
rem :endGetargs

rem USERPATH is a variable local to this batch file
if "%CLASSPATH%"=="" set USERPATH=.
if not "%CLASSPATH%"=="" set USERPATH=%CLASSPATH%
@echo on
echo %ESCJ_ARGS%
java  -Dsimplify=%ESCJ_SIMPLIFY% -classpath "%ESCJAVA_ROOT%\esctools2.jar" escjava.Main -classpath  "%ESCJAVA_ROOT%\jmlspecs.jar;." %ESCJ_STDARGS% %ESCJ_ARGS%
