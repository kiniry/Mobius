// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Scanner;

import java.io.DataInputStream;
import java.io.IOException;

public class ScannerInput {

  /** Input stream for client scanners. */
  
  public String streamName;
  
  DataInputStream rd;

  int charPos, linePos, lineCharPos;
  
  boolean generateEOF;
  boolean closeReader;
  
  public ScannerInput next;
  
  public ScannerInput(String streamName, DataInputStream rd, ScannerInput next, 
                    boolean closeReader, boolean generateEOF) {
  /** Constructor. */
    this.streamName = streamName;
    this.rd = rd;
    this.next = next;
    
    this.charPos = 0;
    this.linePos = 1;
    this.lineCharPos = 0;
    
    this.closeReader = closeReader;
    this.generateEOF = generateEOF;
  }

  public char readChar() throws IOException {
  /** The method to call to get the next character */
    char ch = (char)rd.readByte(); // N.B. readChar would skip every other char !?!
//System.err.print(ch); System.err.print("="); System.err.print((int)ch); System.err.println();
    return ch;
  }
  
  public void advance(char ch) {
    charPos++;
    lineCharPos++;
    if ((int)ch == 13) { // N.B. (ch == '\n') does not detect newlines !?!
      linePos++;
      lineCharPos = 0;
    }
  }
  
  public int available() throws IOException {
    return rd.available();
  }
  
  public void close() throws IOException {
    rd.close();
  }
  
}
