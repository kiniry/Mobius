/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.util;

import ie.ucd.bon.Main;

import java.awt.Point;
import java.awt.image.BufferedImage;
import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;

import javax.imageio.ImageIO;

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
    InputStream istream = getInputStream(filePath);
    if (istream != null) {
      BufferedReader br = new BufferedReader(new InputStreamReader(istream));
      return br;
    } else {
      return null;
    }
  }

  public static InputStream getInputStream(String filePath) {
    return FileUtil.class.getClassLoader().getResourceAsStream(filePath);
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

  public static boolean writeStringToFile(String s, File f) {
    try {
      BufferedWriter bw = new BufferedWriter(new FileWriter(f));
      bw.write(s);
      bw.flush();
      bw.close();
      return true; 
    } catch (IOException ioe) {
      if (Main.isDebug()) {
        ioe.printStackTrace();
      }
      System.out.println("Error writing file " + f.getPath());
      return false;
    }
  }

  public static boolean copyResourceToExternalFile(String filePath, File outputFile) {
    try {
      InputStream is = getInputStream(filePath);
      if (is == null) {
        System.out.println("Couldn't find resource: " + filePath);
        return false;
      }
      BufferedInputStream bis = new BufferedInputStream(is);

      FileOutputStream fos = new FileOutputStream(outputFile);
      BufferedOutputStream bos = new BufferedOutputStream(fos);

      byte[] buf = new byte[bis.available()];
      int i = 0;
      while ((i = bis.read(buf))!= -1) {
        bos.write(buf, 0, i);
      }
      bis.close();
      bos.close();

      return true;
    } catch (IOException ioe) {
      return false;
    }
  }
  
  public static FilenameFilter getSuffixFilenameFilter(final String suffix) {
    return new FilenameFilter() {
      public boolean accept(File dir, String name) {
        return name.endsWith(suffix);
      }
    };
  }
  
  public static boolean deleteAll(File... files) {
    for (File file : files) {
      if (!file.delete()) {
        return false;
      }
    }
    return true;
  }
  
  public static Point getImageDimensions(String imageFilePath) {
    return getImageDimensions(new File(imageFilePath));
  }
  
  public static Point getImageDimensions(File imageFile) {
    try {
      BufferedImage image = ImageIO.read(imageFile);
      if (image == null) {
        System.out.println("Error reading image file: " + imageFile);
        return new Point(-1,-1);
      } else {
        return new Point(image.getWidth(), image.getHeight());
      }
    } catch (IOException e) {
      System.out.println("Error reading image file: " + imageFile);
      return new Point(-1,-1);
    }
  }
}
