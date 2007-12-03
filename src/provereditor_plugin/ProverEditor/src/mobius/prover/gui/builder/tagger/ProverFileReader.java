package mobius.prover.gui.builder.tagger;

import java.io.IOException;
import java.io.Reader;




/**
 * A line reader that has a counter to know how many characters
 * have been read this far.
 */
public class ProverFileReader extends Reader {

  private Reader in = null;

  private char cb[] = new char[8192];
  private int nChars = 0;
  private int nextChar = 0;

  /** If the next character is a line feed, skip it. */
  private boolean fSkipLF;
  
  private int fCount = 0;

  /**
   * Create a buffering character-input stream that uses a default-sized
   * input buffer.
   *
   * @param  in   A Reader
   */
  public ProverFileReader(final Reader in) {
    super(in);
    this.in = in; 
  }

  /** 
   * Check to make sure that the stream has not been closed. 
   */
  private void ensureOpen() throws IOException {
    if (in == null) {
      throw new IOException("Stream closed");
    }
  }

  /**
   * Fill the input buffer.
   */
  private void fill() throws IOException {
    int n;
    do {
      n = in.read(cb, 0, cb.length);
    } while (n == 0);
    if (n > 0) {
      nChars = n;
      nextChar = 0;
    }
  }

  /**
   * Read a single character.
   *
   * @return The character read, as an integer in the range
   *         0 to 65535 (<tt>0x00-0xffff</tt>), or -1 if the
   *         end of the stream has been reached
   * @exception  IOException  If an I/O error occurs
   */
  public int read() throws IOException {
    synchronized (lock) {
      ensureOpen();
      for (;;) {
        if (nextChar >= nChars) {
          fill();
          if (nextChar >= nChars) {
            return -1;
          }
        }
        if (fSkipLF) {
          fSkipLF = false;
          if (cb[nextChar] == '\n') {
            nextChar++;
            continue;
          }
        }
        return cb[nextChar++];
      }
    }
  }

  /**
   * Read characters into a portion of an array, reading from the underlying
   * stream if necessary.
   */
  private int read1(char[] cbuf, int off, int len) throws IOException {
    if (nextChar >= nChars) {
      /* If the requested length is at least as large as the buffer, and
         if there is no mark/reset activity, and if line feeds are not
         being skipped, do not bother to copy the characters into the
         local buffer.  In this way buffered streams will cascade
         harmlessly. */
      if (len >= cb.length && !fSkipLF) {
        return in.read(cbuf, off, len);
      }
      fill();
    }
    if (nextChar >= nChars) {
      return -1;
    }
    if (fSkipLF) {
      fSkipLF = false;
      if (cb[nextChar] == '\n') {
        nextChar++;
        if (nextChar >= nChars) {
          fill();
        }
        if (nextChar >= nChars) {
          return -1;
        }
      }
    }
    final int n = Math.min(len, nChars - nextChar);
    System.arraycopy(cb, nextChar, cbuf, off, n);
    nextChar += n;
    return n;
  }

  /*
   * (non-Javadoc)
   * @see java.io.Reader#read(char[], int, int)
   */
  public int read(char cbuf[], int off, int len) throws IOException {
    synchronized (lock) {
      ensureOpen();
      if ((off < 0) || (off > cbuf.length) || (len < 0) ||
          ((off + len) > cbuf.length) || ((off + len) < 0)) {
        throw new IndexOutOfBoundsException();
      } 
      else if (len == 0) {
        return 0;
      }

      int n = read1(cbuf, off, len);
      if (n <= 0) {
        return n;
      }
      while ((n < len) && in.ready()) {
        final int n1 = read1(cbuf, off + n, len - n);
        if (n1 <= 0) { 
          break;
        }
        n += n1;
      }
      return n;
    }
  }

  /**
   * Read a line of text.  A line is considered to be terminated by any one
   * of a line feed ('\n'), a carriage return ('\r'), or a carriage return
   * followed immediately by a linefeed.
   *
   * @return     A String containing the contents of the line, not including
   *             any line-termination characters, or null if the end of the
   *             stream has been reached
   *
   * @exception  IOException  If an I/O error occurs
   */
  String readLine() throws IOException {
    StringBuffer s = null;
    int startChar;
    fCount = 0;
    synchronized (lock) {
      ensureOpen();
      for (;;) {
        if (nextChar >= nChars) {
          fill();
        }
        if (nextChar >= nChars) { /* EOF */
          if (s != null && s.length() > 0) {
            fCount += s.length();
            return s.toString();
          }
          else {
            return null;
          }
        }
        boolean eol = false;
        char c = 0;
        int i;
  
        /* Skip a leftover '\n', if necessary */
        if (fSkipLF && (cb[nextChar] == '\n')) { 
          nextChar++;
        }
        fSkipLF = false;  
      charLoop:
        for (i = nextChar; i < nChars; i++) {
          c = cb[i];
          if ((c == '\n') || (c == '\r')) {
            fCount++;
            eol = true;
            break charLoop;
          }
        }
        startChar = nextChar;
        nextChar = i;
  
        if (eol) {
          String str;
          if (s == null) {
            str = new String(cb, startChar, i - startChar);
          }
          else {
            s.append(cb, startChar, i - startChar);
            str = s.toString();
          }
          nextChar++;
          if (c == '\r') {
            fCount++;
            fSkipLF = true;
          }
          fCount += str.length();
          return str;
        }
      
        if (s == null) { 
          s = new StringBuffer(80);
        }
        s.append(cb, startChar, i - startChar);
      }
    }
  }

  public int getCount() {
    return fCount;
  }




  /**
   * Tell whether this stream is ready to be read.  A buffered character
   * stream is ready if the buffer is not empty, or if the underlying
   * character stream is ready.
   *
   * @exception  IOException  If an I/O error occurs
   */
  public boolean ready() throws IOException {
    synchronized (lock) {
      ensureOpen();

      /* 
       * If newline needs to be skipped and the next char to be read
       * is a newline character, then just skip it right away.
       */
      if (fSkipLF) {
        /* Note that in.ready() will return true if and only if the next 
         * read on the stream will not block.
         */
        if (nextChar >= nChars && in.ready()) {
          fill();
        }
        if (nextChar < nChars) {
          if (cb[nextChar] == '\n') {
            nextChar++;
          }
          fSkipLF = false;
        } 
      }
      return (nextChar < nChars) || in.ready();
    }
  }


  public boolean markSupported() {
    return false;
  }


  /**
   * Close the stream.
   *
   * @exception  IOException  If an I/O error occurs
   */
  public void close() throws IOException {
    synchronized (lock) {
      if (in == null) {
        return;
      }
      in.close();
      in = null;
      cb = null;
    }
  }

}
