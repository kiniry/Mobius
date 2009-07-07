
package java.lang;

/** JML's specification of java.lang.Thread.
 */
//-@ immutable 
public final class Thread
{
    /*@ public normal_behavior @*/
    public static /*@ pure non_null @*/ Thread currentThread();

    /* dumpStack() is not pure since it writes to output.
    /*@ public normal_behavior @*/
    public static void dumpStack();
}
