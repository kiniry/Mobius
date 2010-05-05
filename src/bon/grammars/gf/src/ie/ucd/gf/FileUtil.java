/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.gf;

import java.awt.Point;
import java.awt.image.BufferedImage;
import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.Reader;
import java.util.Enumeration;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

import javax.imageio.ImageIO;

public final class FileUtil {

  /**
   * Private constructor, cannot be instantiated.
   */
  private FileUtil() { }

  private static final String GF_SOURCE_FOLDERS = "gf-files-folder";
  private static final String GF_SOURCE_RESOURCES = "gf_source/";
  private static final String GF_SOURCE_DESTINATION = getGFFileDirectory();
  
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
    return getInputStream(null, filePath);
  }

  public static InputStream getInputStream(Class<?> c, String filePath) {
    if (c == null) {
      c = FileUtil.class;
    }
    return c.getClassLoader().getResourceAsStream(filePath);
    
    
   
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
      System.out.println("Error writing file " + f.getPath());
      return false;
    }
  }
  
  public static boolean copyFile(File input, File output) {
    try {
      return copyEntirely(new FileInputStream(input), new FileOutputStream(output));
    } catch (FileNotFoundException fnfe) {
      System.out.println("Input file not found: " + input);
      return false;
    }
  }

  public static boolean copyResourceToExternalFile(String filePath, File outputFile) {
    return copyResourceToExternalFile(filePath, outputFile, null);
  }

  public static boolean copyResourceToExternalFile(String filePath, File outputFile, Class<?> c) {
    try {
      InputStream is = getInputStream(c, filePath);
      if (is == null) {
        System.out.println("Couldn't find resource: " + filePath);
        return false;
      }
      FileOutputStream fos = new FileOutputStream(outputFile);
      return copyEntirely(is, fos);
    } catch (FileNotFoundException fnfe) {
      System.out.println("Cannot write to file " + outputFile);
      return false;
    }
  }

  public static boolean copyEntirely(InputStream is, OutputStream os) {
    try {
      BufferedInputStream bis = new BufferedInputStream(is);
      BufferedOutputStream bos = new BufferedOutputStream(os);

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
      @Override
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
  
  
public static boolean copyGFSourceFiles() {
		boolean filesCopied = false;
	    try {
	  			ResourceBundle rb = ResourceBundle.getBundle("gf_source.gf_files");
	  			
	  			Enumeration gfFiles = rb.getKeys();
	  			String sourceDir = "gf_source/"  ;
	  			File gfDirectory = new File(GF_SOURCE_DESTINATION);
	  			if (!gfDirectory.isDirectory()){
	  				if (!gfDirectory.mkdir()){
		  				throw new SecurityException();			
	  				}
	  			}
	  			gfDirectory.deleteOnExit();
	  			while (gfFiles.hasMoreElements()) {
	  			    String key = (String)gfFiles.nextElement();
	  			    String value = rb.getString(key);
	  			    System.out.println("key = " + key + ", " + 
	  					       "value = " + value);
		    	    File dstPath = new File(GF_SOURCE_DESTINATION + value);
		    	    filesCopied = copyResourceToExternalFile(sourceDir + value, dstPath,GF.class);
	  			}

	    } catch (MissingResourceException e) {
	    	System.out.println(e);
		    }
		catch (SecurityException e){
			System.out.println("Could not create Directory " + GF_SOURCE_DESTINATION );
		}
		
		return filesCopied;
	  }

/* (non-Javadoc)
 * @see ie.ucd.gf.api.GfCommands#getGFFileDirectory()
 * Returns the directory where the BON GF files will
 * be copied, to be used by GF.
 */
public static String getGFFileDirectory() {
	
	String filesLocation = "";
	try {
			ResourceBundle rb = ResourceBundle.getBundle("gf-file-location");
			 filesLocation = rb.getString(GF_SOURCE_FOLDERS);
		}catch (MissingResourceException e){
		      System.out.println("Error reading gf.properties " + e);
		}
		return filesLocation;
}

public static boolean removeGFFileDirectory() {
	
	String gfSource = GF_SOURCE_DESTINATION;
	gfSource = gfSource.substring(0,gfSource.length() -1); //remove last forward slash "/"
	System.out.println("Directory to be deleted : " + gfSource);
	File gfDirectory = new File(gfSource);
	return gfDirectory.delete();
}
  

public static boolean updateBONTerms() {
	
	String bonSource = "gf_Source/BONTermsAbs.gf";
	
	File bonTermFile = new File(bonSource);
	return bonTermFile.exists();
	
}
  
  
}
