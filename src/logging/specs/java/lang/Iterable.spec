
package java.lang;


/** JML's specification of java.lang.Iterable.
 */
//-@ immutable 
public interface Iterable
{
    /*@ public normal_behavior @*/
    /*@ pure non_null @*/ Iterator iterator();
}
