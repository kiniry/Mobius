package java.lang;

/** JML's specification of java.lang.Iterable. */
//-@ immutable 
public interface Iterable
{
    /*@ pure non_null @*/ Iterator iterator();
}
