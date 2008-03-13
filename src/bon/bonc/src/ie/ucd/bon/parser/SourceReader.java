/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public final class SourceReader {

  private static SourceReader instance;
  
  private final Map<File,SourceLineReader> readers;
  
  private final List<String> stdInLines;
  
  private SourceReader() {
    readers = new HashMap<File,SourceLineReader>();
    stdInLines = new ArrayList<String>();
  }
  
  public static SourceReader getInstance() {
    if (instance == null) {
      instance = new SourceReader();
    }
    return instance;
  }
  
  public String getSource(File sourceFile, int lineNumber) {
    SourceLineReader reader = readers.get(sourceFile);
    if (reader == null) {
      if (!sourceFile.exists()) {
        return null;
      }
      reader = new SourceLineReader(sourceFile);
      readers.put(sourceFile, reader);
    }
    return reader.getLine(lineNumber);
  }
  
  public String getStandardInputSource(int lineNumber) {
    if (stdInLines.size() == 0) {
      return null;
    }
    if (lineNumber <= stdInLines.size()) {
      return stdInLines.get(lineNumber-1);
    } else {
      return null;
    }
  }
  
  public InputStream readStandardInput() {
    try {
      BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
      StringBuilder sb = new StringBuilder();
      String line;
      while ((line = br.readLine()) != null) {
        sb.append(line);
        stdInLines.add(line);
        sb.append('\n');
      }      
      return new ByteArrayInputStream(sb.toString().getBytes("UTF-8"));
    } catch (IOException ioe) {
      System.out.println("Something went wrong when reading from stdin");
      return null;
    }
  }
  
  public InputStream readFile(File f) throws IOException {
        BufferedReader br = new BufferedReader(new FileReader(f));
        StringBuilder sb = new StringBuilder();
        String line;
        while ((line = br.readLine()) != null) {
          sb.append(line);
          sb.append('\n');
        }      
        return new ByteArrayInputStream(sb.toString().getBytes());
  }
}
