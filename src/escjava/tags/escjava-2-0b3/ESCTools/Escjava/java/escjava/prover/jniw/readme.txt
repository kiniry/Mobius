ADDITIONAL MAKEFILE VARIABLES NEEDED:
(Define in Makefile.local)
CC : the name of your c++ compiler (g++)
CVC_LIB_DIR = /usr/local/lib
CVC_INCLUDE_DIR = /usr/local/include/cvcl
CVC_FLAGS = -DHAVE___GNU_CXX__EXT_HASH_MAP -DHAVE___GNU_CXX__EXT_HASH_SET
JAVA_BIN_DIR = /usr/java/jdk1.5.0_01/bin
JAVA_INCLUDE_DIR = /usr/java/jdk1.5.0_01/include
JAVA_INCLUDE_LINUX = /usr/java/jdk1.5.0_01/include/linux


note:
This assumes that the latest development version of cvcl is installed in its 
default directory.
To compile cvcl, it may be necessary to edit expr_value.h line 317:
remove "ExprValue::"

for debugging purposes, may need to
export LD_LIBRARY_PATH=.:/usr/local/lib
to get this to run


