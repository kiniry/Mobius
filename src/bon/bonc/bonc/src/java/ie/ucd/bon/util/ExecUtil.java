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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import com.google.common.collect.ImmutableList;

public class ExecUtil {

  private final static String[] additionalPaths = { "/bin", "/usr/bin", "/opt/local/bin" };
  
  public static final ExecUtil instance = new ExecUtil(true);
  
  private final Map<File,Set<String>> filesOnPathMap;
  private final Collection<File> pathFiles;

  public ExecUtil(boolean useAdditionalPaths) {
    String pathString = System.getenv("PATH");
    if (pathString == null) {
      pathString = "";
    } else {
      pathString += File.pathSeparator;
    }
    if (useAdditionalPaths) {
      System.out.println("Before: " + pathString);
      pathString += StringUtil.appendWithSeparator(additionalPaths, File.pathSeparator);
      System.out.println("After: " + pathString);
    }
    pathFiles = getPathAsFiles(pathString);
    filesOnPathMap = new HashMap<File,Set<String>>();
    System.out.println(System.getenv());
  }
  
  private String[] createNewEnv() {
    List<String> entries = new ArrayList<String>();
    Map<String,String> env = System.getenv();
    for (Entry<String,String> entry : env.entrySet()) {
      if (entry.equals("PATH")) {
        
      } else {
        entries.add(entry.getKey() + '=' + entry.getValue());
      }
    }
    return ArrayUtil.toArray(entries);
  }

  private static Collection<File> getPathAsFiles(String pathString) {
    String[] parts = pathString.split(File.pathSeparator);
    Collection<File> pathFiles = new ArrayList<File>();
    for (String pathEntry : parts) {
      if (!pathEntry.isEmpty()) {
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
    System.out.println("Path: " + StringUtil.appendWithSeparator(pathFiles, ":"));
    return ImmutableList.copyOf(pathFiles);
  }

  public boolean hasBinaryOnPath(String binaryName, boolean useCache) {
    for (File file : pathFiles) {
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

  public boolean hasBinaryOnPath(String binaryName) {
    return hasBinaryOnPath(binaryName, true);
  }

  public int execWait(String command, boolean outputStdout, boolean outputStderr) {
    return execWait(command, outputStdout ? System.out : null, outputStderr ? System.err : null);
  }

  public int execWait(String command, PrintStream outputStream, PrintStream errStream) {
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

  public int execWaitIgnoreOutput(String command) {
    return execWait(command, false, false);
  }

  public int execWaitAndPrintToStandardChannels(String command) {
    return execWait(command, true, true);
  }

}
