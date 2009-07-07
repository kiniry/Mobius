// $Id: StringWriter.refines-spec 2210 2006-11-28 01:30:20Z chalin $

package java.io;

/* Writer class.
 *
 * From the java spec: 
 * Abstract class for writing to character streams. The only methods that a
 * subclass must implement are write(char[], int, int), flush(), and close().
 * Most subclasses, however, will override some of the methods defined here in
 * order to provide higher efficiency, additional functionality, or both. 
 * (http://java.sun.com/j2se/1.5.0/docs/api/java/io/Writer.html)
 *
 * 
 */

public class Writer extends java.io.Writer {

	// protected Object lock;

	protected /*@ pure @ */ Writer();
	protected /*@ pure @*/ Writer( /*@ non_null @*/ Object lock);
	public void write(int c) throws IOException;
	public void write( /*@ non_null @*/ char[] cbuf) throws IOException;
	public abstract void write(char[] cbuf, int off, int len) throws IOException;

    public /*@ pure @*/ StringWriter();

    public void close()
        throws java.io.IOException;

    public void flush();

    public StringWriter(int Param0);

    public void write(int Param0);

    public void write(/*@non_null*/ char[] Param0, int Param1, int Param2);

    public /*@non_null*/ java.lang.String toString();

    public void write(/*@non_null*/ java.lang.String Param0);

    public void write(/*@non_null*/ java.lang.String Param0, int Param1, int Param2);

    public /*@non_null*/ java.lang.StringBuffer getBuffer();
}
