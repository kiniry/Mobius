
package java.io;

/**
 * JML's specification of java.io.Appendable. java5
 *
 * @author Viliam Holub
 */
public interface Appendable
{
	/*@ ensures \result == this;
	  @*/
	public Appendable append( CharSequence csq)
			throws java.io.IOException;
	
	/*@ public normal_behavior
	  @ 	requires start >= 0;
	  @ 	requires end >= 0;
	  @	  requires start <= end;
	  @	  requires (csq != null) ==> (end <= csq.length());
	  @   assignable objectState;
	  @ 	ensures \result == this;
	  @ also
	  @ public exceptional_behavior
	  @   assignable \nothing;
	  @	  signals_only IndexOutOfBoundsException, IOException;
	  @	  signals (IndexOutOfBoundsException)
	  @			start<0 || end <= 0 || start > end
	  @			|| (csq != null) ==> (end > csq.length());
	  @*/
	public Appendable append(CharSequence csq, int start, int end)
			throws java.io.IOException;
	
	public Appendable append( char c)
			throws java.io.IOException;
}
