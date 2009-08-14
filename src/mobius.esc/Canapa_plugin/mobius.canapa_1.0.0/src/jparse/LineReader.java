/*
 * @(#)$Id: LineReader.java,v 1.2 2004/04/02 05:48:47 james Exp $
 *
 * JParse: a freely available Java parser
 * Copyright (C) 2000,2004 Jeremiah W. James
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * Author: Jerry James
 * Email: james@eecs.ku.edu, james@ittc.ku.edu, jamesj@acm.org
 * Address: EECS Department - University of Kansas
 *          Eaton Hall
 *          1520 W 15th St, Room 2001
 *          Lawrence, KS  66045-7621
 */
package jparse;

import java.io.*;

/**
 * A file reader that can give you a numbered line as a string.  This is
 * useful for printing error messages regarding particular lines in a file.
 * Note that this implementation is <strong>not synchronized</strong>.
 * Concurrent threads should not access a <code>LineReader</code> object
 * without synchronizing between themselves.
 *
 * <p><b>BUG</b>: You always get a newline at the end of the file, even if
 * the file doesn't have one.  This is a limitation of
 * <code>BufferedReader</code>.</p>
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 * @see java.io.BufferedReader
 */
final class LineReader extends Reader {

    /**
     * The maximum number of lines of the file to keep in the cache
     */
    private static final int LINE_CACHE_SIZE = 5;

    /**
     * The line cache
     */
    private final String[] lineCache = new String[LINE_CACHE_SIZE];

    /**
     * The number of valid cache lines
     */
    private int validLines;

    /**
     * The line number (in the file) of the first line in the cache
     */
    private int lineNumber = 1;

    /**
     * The cache line we are currently reading
     */
    private int cacheLine = 0;

    /**
     * The position in the first line in the cache to read next
     */
    private int linePos = 0;

    /**
     * The underlying <code>BufferedReader</code> used to fetch lines from the
     * file
     */
    private final BufferedReader buf;

    /**
     * An indication of whether this stream has been closed
     */
    private boolean closed = false;

    /**
     * The line number of the current mark
     */
    private int markLineNumber = -1;

    /**
     * The column number of the current mark
     */
    private int markLinePos = -1;

    /**
     * Create a new <code>LineReader</code>
     *
     * @param fileName the name of the file to read from
     * @exception IOException if no file with that name can be read or an I/O
     * error occurs during the initial cache fill
     */
    LineReader(final String fileName) throws IOException {
	this(new FileReader(fileName));
    }

    /**
     * Create a new <code>LineReader</code>
     *
     * @param file the file to read from
     * @exception IOException if no such file can be read or an I/O error
     * occurs during the initial cache fill
     */
    LineReader(final File file) throws IOException {
	this(new FileReader(file));
    }

    /**
     * Create a new <code>LineReader</code>
     *
     * @param fd a descriptor for the file to read from
     * @exception IOException if an I/O error occurs during the initial cache
     * fill
     */
    LineReader(final FileDescriptor fd) throws IOException {
	this(new FileReader(fd));
    }

    /**
     * Internal filling of the line cache when a <code>LineReader</code> is
     * first created
     *
     * @param reader the <code>FileReader</code> to use for reading the file
     * @exception IOException if an I/O error occurs
     */
    private LineReader(final FileReader reader) throws IOException {
	buf = new BufferedReader(reader);
	for (validLines = 0; validLines < LINE_CACHE_SIZE; validLines++) {
	    final String line = buf.readLine();
	    if (line == null)
		break;
	    lineCache[validLines] = line;
	}
    }

    /**
     * Called when a line has been read completely.  Either advance the
     * pointer in the cache, or read in a new line if we have exhausted the
     * cache.
     *
     * @exception IOException if an I/O error occurs
     */
    private void lineDone() throws IOException {
	linePos = 0;
	if (cacheLine < validLines - 1) {   // There is more in the cache
	    cacheLine++;
	} else {			    // Need a new line in the cache
	    final String newLine = buf.readLine();
	    if (newLine == null) {
		validLines = 0;		    // EOF
	    } else {
		// Drop the first line in the cache and rotate
		for (int i = 0; i < validLines - 1; i++)
		    lineCache[i] = lineCache[i + 1];
		lineCache[validLines - 1] = newLine;
		lineNumber++;
	    }
	}
    }

    /**
     * Get a particular line from the file
     *
     * @param lineNum the number of the line to fetch
     * @return the line, as a string, or <code>null</code> if it is not in the
     * line cache
     */
    String getLine(final int lineNum) {
	final int index = lineNum - lineNumber;
	return (index < 0 || index >= validLines) ? null : lineCache[index];
    }

    /**
     * Read a single character.  This method will block until a character is
     * available, an I/O error occurs, or the end of the stream is reached. 
     *
     * @return the character read, as an integer in the range 0 to 16383
     * (<code>0x00-0xffff</code>), or -1 if the end of the stream has been
     * reached
     * @exception IOException if an I/O error occurs
     */
    public int read() throws IOException {
	if (closed)
	    throw new IOException("Stream closed");
	if (validLines == 0)
	    return -1;
	final String line = lineCache[cacheLine];
	final char retChar;
	if (linePos < line.length()) {
	    retChar = line.charAt(linePos++);
	} else {
	    retChar = '\n';
	    lineDone();
	}
	return retChar;
    }

    /**
     * Read characters into a portion of an array.  This method will block
     * until some input is available, an I/O error occurs, or the end of the
     * stream is reached.
     *
     * @param cbuf the destination buffer
     * @param off the offset at which to start storing characters
     * @param len the maximum number of characters to read
     * @return the number of characters read, or -1 if the end of the stream
     * has been reached
     * @exception IOException if an I/O error occurs
     */
    public int read(final char[] cbuf, final int off, final int len)
	throws IOException {

	if (closed)
	    throw new IOException("Stream closed");
	if (validLines == 0)
	    return -1;
	int chars = 0;
	while (chars < len && validLines != 0) {
	    final String line = lineCache[cacheLine];
	    final int length = line.length();
	    final int availChars = length + 1 - linePos;  // +1 for newline
	    if (chars + availChars < len) {
		line.getChars(linePos, length, cbuf, off + chars);
		chars += length;
		cbuf[off + chars++] = '\n';
		lineDone();
	    } else {
		final int lastIndex = len - chars + linePos;
		line.getChars(linePos, lastIndex, cbuf, off + chars);
		linePos += len - chars;
		chars = len;
	    }
	}
	return chars;
    }

    /**
     * Tell whether this stream is ready to be read
     *
     * @return <code>True</code> if the next <code>read()</code> is guaranteed
     * not to block for input, <code>false</code> otherwise.  Note that
     * returning <code>false</code> does not guarantee that the next read will
     * block.
     * @exception IOException if an I/O error occurs
     */
    public boolean ready() throws IOException {
	if (closed)
	    throw new IOException("Stream closed");
	return validLines != 0;
    }

    /**
     * Tell whether this stream supports the <code>mark()</code> operation,
     * which it does
     *
     * @return <code>true</code> if <code>mark()</code> is supported,
     * <code>false</code> otherwise
     */
    public boolean markSupported() {
	return true;
    }

    /**
     * Mark the present position in the stream.  Subsequent calls to
     * <code>reset()</code> will attempt to reposition the stream to this
     * point.
     *
     * @param readAheadLimit Limit on the number of characters that may be
     * read while still preserving the mark.  After reading this many
     * characters, attempting to reset the stream may fail.
     * @exception IllegalArgumentException if <var>readAheadLimit</var> is < 0
     * @exception IOException if an I/O error occurs
     */
    public void mark(final int readAheadLimit) throws IOException {
	if (closed)
	    throw new IOException("Stream closed");
	buf.mark(readAheadLimit);
	markLineNumber = lineNumber + cacheLine;
	markLinePos = linePos;
    }

    /**
     * Reset the stream to the most recent mark.
     *
     * @exception IOException if an I/O error occurs, the stream has never
     * been marked, or the mark has been invalidated
     */
    public void reset() throws IOException {
	if (closed)
	    throw new IOException("Stream closed");
	if (markLineNumber < 0)
	    throw new IOException("Stream not marked");
	if (markLineNumber >= lineNumber) {	// Mark is in the line cache
	    cacheLine = markLineNumber - lineNumber;
	    linePos = markLinePos;
	} else {
	    // The mark is not in the line cache.  That means it was rotated
	    // out, which means that we can entirely fill the cache from the
	    // file starting at the mark!
	    buf.reset();
	    for (int i = 0; i < LINE_CACHE_SIZE; i++) {
		lineCache[validLines] = buf.readLine();
	    }
	    validLines = LINE_CACHE_SIZE;
	    lineNumber = markLineNumber;
	    cacheLine = 0;
	    linePos = 0;
	}
	markLineNumber = markLinePos = -1;
    }

    /**
     * Close the stream.  Once a stream has been closed, further
     * <code>read()</code>, <code>ready()</code>, <code>mark()</code>, or
     * <code>reset()</code> invocations will throw an
     * <code>IOException</code>. Closing a previously-closed stream, however,
     * has no effect.
     *
     * @exception IOException if an I/O error occurs
     */
    public void close() throws IOException {
	closed = true;
	buf.close();
    }
}
