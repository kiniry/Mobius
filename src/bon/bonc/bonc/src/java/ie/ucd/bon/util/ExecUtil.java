/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.ImmutableList;

public class ExecUtil {

  private static List<String> path;
  private static List<File> pathFiles;
  private static final Map<File,Set<String>> filesOnPathMap = new HashMap<File,Set<String>>();
  
  public static List<String> getPath() {
    if (path == null) {
      String pathString = System.getenv("PATH");
      if (pathString != null) {
        path = Arrays.asList(pathString.split(File.pathSeparator));
      } else {
        path = Collections.emptyList();
      }
    }
    return path;
  }
  
  public static List<File> getPathAsFiles() {
    if (pathFiles == null) {
      pathFiles = new ArrayList<File>();
      for (String pathEntry : getPath()) {
        try {
          File file = new File(pathEntry);
          if (file.isDirectory()) {
            pathFiles.add(file);
          }
        } catch (Exception e) {
          //Do nothing
        }
      }
    }
    return ImmutableList.copyOf(pathFiles);
  }
  
  public static boolean hasBinaryOnPath(String binaryName, boolean useCache) {
    for (File file : getPathAsFiles()) {
      Set<String> fileNames = null;
      boolean foundInCache = false;
      if (useCache) {
        fileNames = filesOnPathMap.get(fileNames);
        foundInCache = fileNames != null; 
      }
      if (fileNames == null) {
        fileNames = new HashSet<String>();
        fileNames.addAll(Arrays.asList(file.list()));
      }
      if (useCache && !foundInCache) {
        filesOnPathMap.put(file, fileNames);
      }
      if (fileNames.contains(binaryName)) {
        return file.canExecute();
      }
    }
    return false;
  }
  
  public static boolean hasBinaryOnPath(String binaryName) {
    return hasBinaryOnPath(binaryName, true);
  }

  public static int execWait(String command, boolean outputStdout, boolean outputStderr) {
    return execWait(command, outputStdout ? System.out : null, outputStderr ? System.err : null);
  }
  
  public static int execWait(String command, PrintStream outputStream, PrintStream errStream) {
    try {
      Runtime runtime = Runtime.getRuntime();
      Process process = runtime.exec(command);
      
      if (outputStream != null) {
        BufferedReader or = new BufferedReader(new InputStreamReader(process.getInputStream()));
        String lineo;
        while ((lineo = or.readLine()) != null) {
          outputStream.println(lineo);
        }
      }
      
      if (errStream != null) {
        BufferedReader er = new BufferedReader(new InputStreamReader(process.getErrorStream()));
        String linee;
        while ((linee = er.readLine()) != null) {
          errStream.println(linee);
        }
      }
      
      return process.waitFor();
    } catch (IOException ioe) {
      return 1;
    } catch (InterruptedException ie) {
      return 1;
    }
  }
  
  public static int execWaitIgnoreOutput(String command) {
    return execWait(command, false, false);
  }
  
  public static int execWaitAndPrintToStandardChannels(String command) {
    return execWait(command, true, true);
  }
  
}
