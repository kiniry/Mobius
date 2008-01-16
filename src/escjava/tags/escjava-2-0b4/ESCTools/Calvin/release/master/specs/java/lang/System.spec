/* ESC/Java interface of java.lang.System */

package java.lang;

import java.io.*;
import java.util.Properties;

public final class System {
    public final static /*@non_null*/ InputStream in;

    public final static /*@non_null*/ PrintStream out;

    public final static /*@non_null*/ PrintStream err;

    public static void setIn(InputStream in);

    public static void setOut(PrintStream out);

    public static void setErr(PrintStream err);

    public static void setSecurityManager(SecurityManager s);

    public static SecurityManager getSecurityManager();

    public static native long currentTimeMillis();

    //@ requires src != null;
    //@ requires dst != null;
    //@ requires 0 <= length;
    //@ requires 0 <= src_position
    //@ requires 0 <= dst_position
    //@ requires src_position+length <= \dttfsa(Object[], "identity", src).length;
    //@ requires dst_position+length <= \dttfsa(Object[], "identity", dst).length;
    //@ modifies \dttfsa(Object[], "identity", dst)[*];
    /*@ ensures
        (\forall int i;
           0 <= i-dst_position && i-dst_position < length
          ==>
	   \dttfsa(Object[], "identity", dst)[i] ==
	   \old(\dttfsa(Object[], "identity", src)[src_position+i-dst_position])
	); */
    /*@ ensures
        (\forall int i;
           0 > i-dst_position || i-dst_position >= length
          ==>
	   \dttfsa(Object[], "identity", dst)[i] ==
	   \old(\dttfsa(Object[], "identity", dst)[i])
	); */
    public static native void arraycopy(Object src, int src_position,
                                        Object dst, int dst_position,
                                        int length);

    public static native int identityHashCode(Object x);

    //@ ensures \result != null;
    public static Properties getProperties();

    //@ requires props != null;  // Javadoc spec is wrong!!
    public static void setProperties(Properties props);

    public static String getProperty(/*@non_null*/ String key);

    //@ ensures def!=null ==> \result!=null;
    public static String getProperty(/*@non_null*/ String key, String def);
    
    public static String setProperty(/*@non_null*/ String key,
				     /*@non_null*/ String value);
    
    public static String getenv(String name);

    //@ ensures false
    public static void exit(int status);

    public static void gc();

    public static void runFinalization();

    public static void runFinalizersOnExit(boolean value);

    public static void load(/*@non_null*/ String filename);

    public static void loadLibrary(/*@non_null*/ String libname);

    public static native String mapLibraryName(String libname);

    static native Class getCallerClass();
}
