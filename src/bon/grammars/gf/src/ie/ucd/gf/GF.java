package ie.ucd.gf;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;


public class GF {
	
  private static final String BINARY_PATH = "binaries/";
  private static final String OSX_BINARY = "gf-3.1-mac";
  private static final String LINUX_X32_BINARY = "gf-3.1-linux-i486";
  private static final String LINUX_X64_BINARY = "gf-3.1-linux-x86_64";
  private static final String WINDOWS_BINARY = "gf.exe";
 
  
  public static void main(String[] args) throws IOException {
    GFProcess proc = createPlatformSpecificProcess();
    if (proc != null) {
      proc.blockUntilOutputReady(); //There should be some output immediately
      System.out.print(proc.getAllBufferedOutput());
      
      BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
      while (proc.isAlive()) {
        System.out.print(GFProcess.PROMPT);
        String line = reader.readLine();
        String response = proc.enterCommand(line);
        System.out.print(response);
      }
      System.out.println("Proc is dead.");
    }
  }
  
  public static GFProcess createPlatformSpecificProcess() {
    if (SystemUtil.IS_OS_WINDOWS) {
      return createProcess(WINDOWS_BINARY);
    } else if (SystemUtil.IS_OS_MAC) {
      return createProcess(OSX_BINARY);
    } else if (SystemUtil.IS_OS_LINUX_32) {
      System.out.println("x32");
      return createProcess(LINUX_X32_BINARY);
    } else if (SystemUtil.IS_OS_LINUX_64) {
      System.out.println("x64");
      return createProcess(LINUX_X64_BINARY);
    } else {
      System.out.println("Unrecognised operating system. Unable to create gf process.");
      return null;
    }
  }

  public static GFProcess createProcess(String binaryName) {
    try {
      File f = File.createTempFile(binaryName, Long.toString(System.nanoTime()));
      if (!FileUtil.copyResourceToExternalFile(BINARY_PATH + binaryName, f, GF.class)) {
        return null;
      }
      f.setExecutable(true);
      f.deleteOnExit();
      return new GFProcess(f.getAbsolutePath());
    } catch (IOException ioe) {
      System.out.println(ioe);
      ioe.printStackTrace();
      return null;
    }
  }
  

  
}
