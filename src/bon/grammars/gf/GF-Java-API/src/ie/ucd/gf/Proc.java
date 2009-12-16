package ie.ucd.gf;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;

import org.apache.commons.lang.SystemUtils;

public class Proc {
 
  private static final String BINARY_PATH = "binaries/";
  private static final String OSX_BINARY = "gf-3.0-mac-noreadline";
  private static final String LINUX_BINARY = "gf";
  private static final String WINDOWS_BINARY = "gf.exe";
  
  public static void main(String[] args) throws IOException {
    AProcess proc = createPlatformSpecificProcess();
    if (proc != null) {
      System.out.print(proc.getAllBufferedOutput());
      
      BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
      while (proc.isAlive()) {
        String line = reader.readLine();
        String response = proc.enterCommand(line);
        System.out.print(response);
      }
      
    }
  }
  
  public static AProcess createPlatformSpecificProcess() {
    if (SystemUtils.IS_OS_WINDOWS) {
      return createProcess(WINDOWS_BINARY);
    } else if (SystemUtils.IS_OS_MAC) {
      return createProcess(OSX_BINARY);
    } else if (SystemUtils.IS_OS_LINUX) {
      return createProcess(LINUX_BINARY);
    } else {
      System.out.println("Unrecognised operating system. Unable to create gf process.");
      return null;
    }
  }

  public static AProcess createProcess(String binaryName) {
    try {
      File f = File.createTempFile(binaryName, Long.toString(System.nanoTime()));
      if (!FileUtil.copyResourceToExternalFile(BINARY_PATH + binaryName, f, Proc.class)) {
        return null;
      }
      f.setExecutable(true);
      f.deleteOnExit();
      return new AProcess(f.getAbsolutePath());
    } catch (IOException ioe) {
      System.out.println(ioe);
      ioe.printStackTrace();
      return null;
    }
  }
  
}
