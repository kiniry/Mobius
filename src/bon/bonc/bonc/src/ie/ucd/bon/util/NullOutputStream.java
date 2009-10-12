/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.util;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;

public class NullOutputStream extends OutputStream {

  private static PrintStream instance;

  public static PrintStream getNullPrintStreamInstance() {
    if (instance == null) {
      instance = new PrintStream(new NullOutputStream());
    }
    return instance;
  }

  @Override
  public void close() throws IOException {
  }

  @Override
  public void flush() throws IOException {
  }

  @Override
  public void write(byte[] b, int off, int len) throws IOException {
  }

  @Override
  public void write(byte[] b) throws IOException {
  }

  @Override
  public void write(int b) throws IOException {
  }

}
