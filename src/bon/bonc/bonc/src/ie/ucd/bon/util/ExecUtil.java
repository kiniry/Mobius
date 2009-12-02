package ie.ucd.bon.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
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
    try {
      Runtime runtime = Runtime.getRuntime();
      Process process = runtime.exec(command);
      
      if (outputStdout) {
        BufferedReader or = new BufferedReader(new InputStreamReader(process.getInputStream()));
        String lineo;
        while ((lineo = or.readLine()) != null) {
          System.out.println(lineo);
        }
      }
      
      if (outputStderr) {
        BufferedReader er = new BufferedReader(new InputStreamReader(process.getErrorStream()));
        String linee;
        while ((linee = er.readLine()) != null) {
          System.err.println(linee);
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
