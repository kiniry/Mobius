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
  private final static String WINDOWS_BINARY_EXTENSION = ".exe";
  
  
  public static final ExecUtil instance = new ExecUtil(true);
  
  private final Map<File,Set<String>> filesOnPathMap;
  private final Map<String,File> binariesOnPathMap;
  private final Collection<File> pathFiles;
  private final String[] newEnv;

  public ExecUtil(boolean useAdditionalPaths) {
    String pathString = getCaseInsensitiveEnvironmentVariable("PATH");
    if (pathString == null) {
      pathString = "";
    } else {
      pathString += File.pathSeparator;
    }
    if (useAdditionalPaths) {
      pathString += StringUtil.appendWithSeparator(additionalPaths, File.pathSeparator);
    }
    pathFiles = getPathAsFiles(pathString);
    filesOnPathMap = new HashMap<File,Set<String>>();
    binariesOnPathMap = new HashMap<String,File>();
    newEnv = createNewEnv();
  }
  
  private String[] createNewEnv() {
    List<String> entries = new ArrayList<String>();
    Map<String,String> env = System.getenv();
    
    for (Entry<String,String> entry : env.entrySet()) {
      if (entry.getKey().equalsIgnoreCase("PATH")) {
        entries.add(entry.getKey() + "=" + StringUtil.appendWithSeparator(pathFiles, File.pathSeparator));
      } else {
        entries.add(entry.getKey() + '=' + entry.getValue());
      }
    }
    return entries.toArray(new String[entries.size()]);
  }

  private static Collection<File> getPathAsFiles(String pathString) {
    String[] parts = pathString.split(File.pathSeparator);
    Collection<File> pathFiles = new ArrayList<File>();
    for (String pathEntry : parts) {
      if (pathEntry.length() > 0) {
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

  public boolean hasBinaryOnPath(String binaryName, boolean useCache) {
    if (IS_WINDOWS) {
      return hasBinaryOnPathNoAddExtension(binaryName, useCache) || hasBinaryOnPathNoAddExtension(binaryName + WINDOWS_BINARY_EXTENSION, useCache);
    } else {
      return hasBinaryOnPathNoAddExtension(binaryName, useCache);
    }    
  }
  
  private boolean hasBinaryOnPathNoAddExtension(String binaryName, boolean useCache) {
    for (File file : pathFiles) {
      Set<String> fileNames = null;
      boolean foundInCache = false;
      if (useCache) {
        fileNames = filesOnPathMap.get(file);
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
        String path = file.getAbsolutePath();
        path += path.endsWith(File.separator) ? "" : File.separator;
        path += binaryName;
        File binary = new File(path);
        if (binary.canExecute()) {
          binariesOnPathMap.put(binaryName, binary);
          return true;
        }
      }
    }
    return false;
  }

  public boolean hasBinaryOnPath(String binaryName) {
    return hasBinaryOnPath(binaryName, true);
  }
  
  public String findAbsoluteCommandPath(String command) {
    if (!hasBinaryOnPath(command)) {
      return command; //Return unchanged
    } else {
      File newCmd = binariesOnPathMap.get(command);
      return newCmd == null ? command : newCmd.getAbsolutePath();
    }
  }

  public int execWait(String command, boolean outputStdout, boolean outputStderr) {
    return execWait(command, outputStdout ? System.out : null, outputStderr ? System.err : null);
  }

  public int execWait(String command, PrintStream outputStream, PrintStream errStream) {
    try {
      Runtime runtime = Runtime.getRuntime();
      
      String[] commandParts = command.split("\\s+");
      commandParts[0] = findAbsoluteCommandPath(commandParts[0]);
      
      Process process = runtime.exec(commandParts, newEnv);

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
      System.out.println("IOException: " + ioe);
      return 1;
    } catch (InterruptedException ie) {
      System.out.println("InterruptedException: " + ie);
      return 1;
    }
  }

  public int execWaitIgnoreOutput(String command) {
    return execWait(command, false, false);
  }

  public int execWaitAndPrintToStandardChannels(String command) {
    return execWait(command, true, true);
  }
  
  public static final boolean IS_WINDOWS = System.getProperty("os.name").startsWith("Windows");

  public static String getCaseUsedForEnvironmentVariable(String varName) {
    Map<String,String> env = System.getenv();
    String[] possibilities = { varName.toUpperCase(), varName.toLowerCase(), varName.toUpperCase().charAt(0) + varName.toLowerCase().substring(1) };
    for (String possibility : possibilities) {
      String var = env.get(possibility);
      if (var != null) {
        return possibility;
      }
    }
    return null;
  }
  
  public static String getCaseInsensitiveEnvironmentVariable(String varName) {
    Map<String,String> env = System.getenv();
    String[] possibilities = { varName.toUpperCase(), varName.toLowerCase(), varName.toUpperCase().charAt(0) + varName.toLowerCase().substring(1) };
    for (String possibility : possibilities) {
      String var = env.get(possibility);
      if (var != null) {
        return var;
      }
    }
    return null;
  }
  
}
