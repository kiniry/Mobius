/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.prover;

import java.io.OutputStream;
import java.io.FilterOutputStream;
import java.io.IOException;


/**
  * This class is a FilterOutputStream class designed for LISP-like
  * input; it pretty prints the output by inserting spaces and newlines
  * into the stream.
  *
  * @author  David Cok
  */

public class PPOutputStream extends FilterOutputStream {

    int parenDepth = 0;
    boolean inComment = false;
    static final int lp = '(';
    static final int rp = ')';

    /**
     * Creates an output stream filter built on top of an
     * underlying output streams.
     *
     * @param   out   the underlying output stream
     */
    public PPOutputStream(/*@ non_null */ OutputStream out) {
        super(out);
    }

    /**
     * Writes the specified <code>byte</code> to this output stream. 
     * <p>
     * Implements the abstract <tt>write</tt> method of <tt>OutputStream</tt>. 
     *
     * @param      b   the <code>byte</code>.
     * @exception  IOException  if an I/O error occurs.
     */
    public void write(int b) throws IOException {
	if (inComment) {
		super.write(b);
		if (b == '\n' || b == '\r') {
			inComment = false;
		} else {
			return;
		}
	}
	if (b == ';') {
		inComment = true;
		super.write(b);
		return;
	}
	if (b == lp) {
	    if (!recentNL) {
		super.write('\n'); //FIXME - multiplatform ???
		int n = 2*parenDepth;
		while (--n >= 0) super.write(' ');
	    }
            ++parenDepth;
        }

	if (b == rp) {
	    super.write(b);
            super.write('\n'); //FIXME - multiplatform ???
            --parenDepth;
            int n = 2*parenDepth;
            while (--n >= 0) super.write(' ');
	    recentNL = true;
	} else if (b == ' ' || b == '\t') {
	    if (!recentNL) super.write(b);
	} else if (b == '\n' || b == '\r') {
	    if (!recentNL) {
		super.write(b);
		int n = 2*parenDepth;
		while (--n >= 0) super.write(' ');
		if (parenDepth > 0) recentNL = true;
	    }
	} else {
	    super.write(b);
	    recentNL = false;
        }

    }

    boolean recentNL = false;
    /**
     * Writes <code>b.length</code> bytes to this output stream. 
     * <p>
     *
     * @param      b   the data to be written.
     * @exception  IOException  if an I/O error occurs.
     * @see        java.io.FilterOutputStream#write(byte[], int, int)
     */
    public void write(byte b[]) throws IOException {
        write(b,0,b.length);
    }

    /**
     * Writes <code>len</code> bytes from the specified 
     * <code>byte</code> array starting at offset <code>off</code> to 
     * this output stream. 
     * <p>
     *
     * @param      b     the data.
     * @param      off   the start offset in the data.
     * @param      len   the number of bytes to write.
     * @exception  IOException  if an I/O error occurs.
     * @see        java.io.FilterOutputStream#write(int)
     */
/*
    public void write(byte b[], int off, int len) throws IOException {
        int e = off+len;
	int n = len;
	int i = off;
	while (i<e) {
	    byte bb = b[i];
	    if (bb == lp) {
                super.write(b,off,i-off);
                off = i;
                super.write('\n'); //FIXME - multiplatform ???
                int nn = 2*parenDepth;
                while (--nn >= 0) super.write(' ');
                ++parenDepth;
                ++i;

            } else if (bb == rp) {
                ++i;
                super.write(b,off,i-off);
                off = i;
                --parenDepth;
                super.write('\n'); //FIXME - multiplatform ???
                int nn = 2*parenDepth;
                while (--nn >= 0) super.write(' ');

            } else {
                ++i;
            }
        }
        super.write(b, off, e-off);
    }
*/
    /**
     * Flushes this output stream and forces any buffered output bytes 
     * to be written out to the stream. 
     * <p>
     *
     * @exception  IOException  if an I/O error occurs.
     * @see        java.io.FilterOutputStream#out
     */
    public void flush() throws IOException {
	super.flush();
    }

    /**
     * Closes this output stream and releases any system resources 
     * associated with the stream. 
     * <p>
     *
     * @exception  IOException  if an I/O error occurs.
     * @see        java.io.FilterOutputStream#flush()
     * @see        java.io.FilterOutputStream#out
     */
    public void close() throws IOException {
	try {
	  flush();
	} catch (IOException ignored) {
	}
	super.close();
    }
}
