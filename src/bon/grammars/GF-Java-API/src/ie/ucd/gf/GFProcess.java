package ie.ucd.gf;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

public class GFProcess {
  private static final String LINE_SEPARATOR = System.getProperty ("line.separator");
  private static final int WAIT_TIME = 10;

  public static final String PROMPT = "\n> ";

  private final Process process;
  private final BufferedWriter bow;
  private final BufferedReader bir;
  private final BufferedReader ber;

  private final StringBuffer readInput;

  /**
   * Create a new gf process using the given command. 
   * @param cmd the path (most likely absolute) to the gf executable to use
   * @throws IOException
   */
  public GFProcess(String cmd) throws IOException {
    process = new ProcessBuilder(cmd).start();
    bow = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
    bir = new BufferedReader(new InputStreamReader(process.getInputStream()));
    ber = new BufferedReader(new InputStreamReader(process.getErrorStream()));

    readInput = new StringBuffer();

    //Setup a thread to constantly copy characters from the std input reader to
    //the StringBuffer readInput
    new Thread(new Runnable() {
      public void run() {
        while(isAlive()) {
          synchronized (readInput) {
            try {
              while(bir.ready()) {
                char c = (char)bir.read();
                readInput.append(c);
              }
            } catch (IOException ioe) {
              ioe.printStackTrace();
              break;
            }
          }
          try {
            Thread.sleep(WAIT_TIME);
          } catch (InterruptedException e) {
            e.printStackTrace();
          }
        }
      }
    }).start();
  }

  /**
   * Get all buffered std output from gf. Removes the trailing prompt, if there is one.
   * @return
   */  
  public String getAllBufferedOutput() {
    String read;
    synchronized (readInput) {
      read = readInput.toString();
      readInput.delete(0, readInput.length());
    }
    if (read.endsWith(PROMPT)) {
      read = read.substring(0, read.length() - PROMPT.length());
    }
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

  /**
   * Give the provided input to the gf process
   * @param input
   * @throws IOException
   */
  public void giveInput(String input) throws IOException {
    bow.write(input);
    bow.flush();
  }

  /**
   * Block until either gf gives us a prompt to indicate it's ready for further input,
   * or until the process dies (e.g. in the case of issuing "quit")
   * @throws IOException
   */
  public void blockUntilOutputReady() throws IOException {
    while (!atPrompt() && isAlive()) {
      try {
        Thread.sleep(WAIT_TIME);
      } catch (InterruptedException e) {
        e.printStackTrace();
      }
    }
  }

  /**
   * Is the gf process currently at a prompt (i.e. not processing and waiting for further input/commands)?
   * @return
   */
  public boolean atPrompt() {
    synchronized (readInput) {
      return readInput.length() >= 3 && readInput.substring(readInput.length()-PROMPT.length(), readInput.length()).equals(PROMPT);
    }
  }

  /**
   * Enter a command to GF and receive the response. The response will not contain the trailing prompt,
   * if there is one.
   * @param command the command to issue.
   * @return the response from gf, as a String.
   * @throws IOException
   */
  public String enterCommand(String command) throws IOException {
    giveInput(command + LINE_SEPARATOR);
    blockUntilOutputReady();
    return getAllBufferedOutput();
  }

  /**
   * Is the process still alive?
   * TODO Can/should we respawn? This is not trivial due to what must be loaded in.
   * @return
   */
  public boolean isAlive() {
    try {
      process.exitValue();
      return false;
    } catch (IllegalThreadStateException itse) {
      return true;
    }
  }
}
