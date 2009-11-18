/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;

public final class FileUtil {

  /**
   * Private constructor, cannot be instantiated.
   */
  private FileUtil() { }

  public static boolean checkDirExists(File dir) {
    if (dir.isDirectory()) {
      return true;
    } else {
      return dir.mkdirs();
    }
  }

  public static boolean checkDirExists(String dirPath) {
    return checkDirExists(new File(dirPath));

  }

  public static Reader getResourceReader(String filePath) {
    InputStream istream = new FileUtil().getClass().getClassLoader().getResourceAsStream(filePath);
    if (istream != null) {
      BufferedReader br = new BufferedReader(new InputStreamReader(istream));
      return br;
    } else {
      return null;
    }
  }

  public static String readToString(Reader r) throws IOException {
    if (r == null) {
      throw new IOException();
    }
    StringBuilder sb = new StringBuilder();
    int c;
    while ((c = r.read()) != -1) {
      sb.append((char)c);
    }
    return sb.toString();
  }

  public static String readToString(File file) throws IOException {
    return readToString(new BufferedReader(new FileReader(file)));
  }
  
  public static String readToString(String filePath) throws IOException {
    Reader r = getResourceReader(filePath);
    if (r == null) {
      throw new FileNotFoundException("File " + filePath + " does not exist.");
    } else {
      return readToString(r);
    }
  }
  
  public static void writeStringToFile(String s, File f) throws IOException {
    BufferedWriter bw = new BufferedWriter(new FileWriter(f));
    bw.write(s);
    bw.flush();
    bw.close();
  }

}
