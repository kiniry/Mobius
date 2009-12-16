package ie.ucd.gf;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

public class AProcess {
  private static final String LINE_SEPARATOR = System.getProperty ("line.separator");
  private static final int WAIT_TIME = 10;

  private final Process process;
  private final BufferedWriter bow;
  private final BufferedReader bir;
  private final BufferedReader ber;

  public AProcess(String cmd) throws IOException {
    process = new ProcessBuilder(cmd).start();
    bow = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
    bir = new BufferedReader(new InputStreamReader(process.getInputStream()));
    ber = new BufferedReader(new InputStreamReader(process.getErrorStream()));
  }

  public String getAllBufferedOutput() {
    String read = readAll(bir);
    return read;
  }

  public String getAllBufferedErrorOutput() {
    return readAll(ber);
  }

  private static String readAll(BufferedReader reader) {
    StringBuilder sb = new StringBuilder();
    try {
      while(reader.ready()) {
        char c = (char)reader.read();
        sb.append(c);
      }
    } catch (IOException ioe) {
      ioe.printStackTrace();
    }
    return sb.toString();
  }

  public void giveInput(String input) throws IOException {
    bow.write(input);
    bow.flush();
  }

  public void blockUntilOutputReady() throws IOException {
    //System.out.println("Blocking");
    while (!bir.ready()) {
      try {
        Thread.sleep(WAIT_TIME);
      } catch (InterruptedException e) {
        e.printStackTrace();
      }
    }
    //System.out.println("Done blocking");
  }

  public String enterCommand(String command) throws IOException {
    giveInput(command + LINE_SEPARATOR);
    blockUntilOutputReady();
    return getAllBufferedOutput();
  }

  public boolean isAlive() {
    try {
      process.exitValue();
      return false;
    } catch (IllegalThreadStateException itse) {
      return true;
    }
  }
}
