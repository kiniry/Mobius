/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.source;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Manages reading from Files as well as from standard input.
 * @author fintan
 *
 */
public final class SourceReader {
  
  /** Singleton instance of SourceReader */
  private static SourceReader instance;
  
  /** Mapping Files to SourceLineReaders */
  private final Map<File,SourceLineReader> readers;
  
  /** The lines read from standard input (if any) */
  private final List<String> stdInLines;

  /**
   * Construct a new SourceReader. Simply initialise the contained data structures.
   */
  private SourceReader() {
    readers = new HashMap<File,SourceLineReader>();
    stdInLines = new ArrayList<String>();
  }
  
  /**
   * Get the singleton instance of SourceReader
   * @return
   */
  public static SourceReader getInstance() {
    if (instance == null) {
      instance = new SourceReader();
    }
    return instance;
  }
  
  /**
   * 
   * @param sourceFile
   * @param lineNumber
   * @return
   */
  public String getSource(File sourceFile, int lineNumber) {
    if (sourceFile == null) {
      return getStandardInputSource(lineNumber);
    } else {
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
  }
  
  /**
   * 
   * @param lineNumber
   * @return
   */
  private String getStandardInputSource(int lineNumber) {
    if (stdInLines.size() == 0) {
      return null;
    }
    if (lineNumber <= stdInLines.size()) {
      return stdInLines.get(lineNumber-1);
    } else {
      return null;
    }
  }
  
  /**
   * 
   * @return
   */
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
  
  /**
   * Read from a provided File, creating an InputStream to facilitate this.
   * @param f the File to read from.
   * @return an InputStream to read the given File's contents.
   * @throws IOException if an IOException occurs whilst reading from the given file.
   */
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
