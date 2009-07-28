// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Scanner;

public class Location {
// "Location" represents a location in a stream. "chr" is the character 
// position within the stream. "line" is  the line position within the stream, 
// and "lineChar" is the character position within that line. *)

  public String streamName;
  public int chr;
  public int line, lineChar;

  public Location(String streamName, int chr, int line, int lineChar) {
  // Constructor.
    this.streamName = streamName;
    this.chr = chr;
    this.line = line;
    this.lineChar = lineChar;
  }
  
  public String streamMsg() {
    return "(stream " + streamName + ")";
  }
  
  public String absoluteCharMsg() {
    return "(char " + Integer.toString(chr) + ")";
  }
  
  public String lineCharMsg() {
    return 
      "(line " + Integer.toString(line) + 
      ", char " + Integer.toString(lineChar) + ")";
  }
  
  public String absoluteCharRangeMsg(Location endInfo) {
    return 
      (chr == endInfo.chr)
      ? absoluteCharMsg()
      : ("(chars " + Integer.toString(chr) + 
          ".." + Integer.toString(endInfo.chr) + ")");
  }
  
  public String lineCharRangeMsg(Location endInfo) {
    return lineCharMsg() + ".." + endInfo.lineCharMsg();
  }
  
  public String streamAbsoluteCharMsg() {
    return streamMsg() + " " + absoluteCharMsg();
  }
  
  public String streamLineCharMsg() {
    return streamMsg() + " " + lineCharMsg();
  }
  
  public String streamAbsoluteCharRangeMsg(Location endInfo) {
    return streamMsg() + " " + absoluteCharRangeMsg(endInfo);
  }
  
  public String streamLineCharRangeMsg(Location endInfo) {
    return streamMsg() + " " + lineCharRangeMsg(endInfo);
  }
}

