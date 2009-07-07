
package java.io;

/**
 * JML's specification of java.io.Writer. java5
 *
 * @author Viliam Holub
 */
public class Writer
		implements java.io.Appendable, java.io.Closeable, java.io.Flushable
{

	// protected Object lock;

	protected /*@ pure @*/ Writer();

	protected /*@ pure @*/ Writer( /*@ non_null @*/ Object lock);

	public void write( int c)
			throws java.io.IOException;

	public void write( /*@ non_null @*/ char[] cbuf)
			throws java.io.IOException;
	
	//@ requires 0 <= off;
	//@ requires 0 <= len;
	public abstract void write( /*@ non_null @*/ char[] cbuf, int off, int len)
			throws java.io.IOException;

	public void write( /*@ non_null @*/ String str)
			throws java.io.IOException;
	
	/*@ requires 0 <= off;
	  @ requires 0 <= len;
	  @*/
	public void write( /*@ non_null @*/ String str, int off, int len)
			throws java.io.IOException;
	
	public Writer append( CharSequence csq)
			throws java.io.IOException;

	public Writer append( CharSequence csq, int start, int end)
			throws java.io.IOException;
	
	public Writer append( char c)
			throws java.io.IOException;
	
	public abstract void flush()
			throws java.io.IOException;
	
	public abstract void close()
			throws java.io.IOException;
}
