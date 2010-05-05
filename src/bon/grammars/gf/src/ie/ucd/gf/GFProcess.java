package ie.ucd.gf;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

public class GFProcess {

	
  private static final String LINE_SEPARATOR = System.getProperty ("line.separator");
  private static final int WAIT_TIME = 10;

  public static final String PROMPT = "> ";

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
   * Enter a command to GF and receive the response. The response will not contain the trailing prompt,
   * if there is one.
   * @param command the command to issue.
   * @return the response from gf, as a String.
   * @throws IOException
   */
  public String importLanguage(String command) throws IOException {
    giveInput(command + LINE_SEPARATOR);
    blockUntilOutputReady();
    return returnImportResponse(getAllBufferedOutput());
  }
  


  private String returnImportResponse(String output) {
	  
	  int linking = output.indexOf("linking ... OK");
	  if (linking != -1){
		  int language = output.indexOf("Languages:",linking);
		  output = output.substring(language, output.indexOf(LINE_SEPARATOR, language));
		 
	  }	
	return output;
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
    return returnGFResponse(getAllBufferedOutput());
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
  
  /**
   * Takes the Buffered output from GF and returns
   * the response to the request
   * @param output
   * @return
   */
  	public String returnGFResponse(String output){
	  
  	/**
  	 * The GF response may have multiple translations. We
  	 * are returning the last translation. The last translation
  	 * is followed by two blank lines, a time taken for the query 
  	 * i.e 9007 msec, a line with "BON>" , 
  	 *  0 msec and another line with "BON>". The following procedure
  	 *  removes these lines in order to take the last 
  	 *  translation from the output. 
  	 * 	
  	 */
  		
	  int lastMsec = output.lastIndexOf("msec");
	  output = output.substring(0,lastMsec);
	  lastMsec = output.lastIndexOf("msec");
	  output = output.substring(0,lastMsec);
	  int lastReturn = output.lastIndexOf(LINE_SEPARATOR);
	  output = output.substring(0,lastReturn);
	  lastReturn = output.lastIndexOf(LINE_SEPARATOR);
	  output = output.substring(0,lastReturn);
	  lastReturn = output.lastIndexOf(LINE_SEPARATOR);
	  output = output.substring(0,lastReturn);
	  String returnedSentence = output.substring(output.lastIndexOf(LINE_SEPARATOR) + 2 ,lastReturn);
	  return removeToBe(returnedSentence);
  }
  	
  	
    /**
     * Quits the GF Process
     * @throws IOException
     */

  	public void quitProcess() throws IOException {
  		  //giveInput("q" + LINE_SEPARATOR);
  		process.destroy();
  		if (!FileUtil.removeGFFileDirectory()){
  			System.out.println("Could not delete GF Source Files from : " + FileUtil.getGFFileDirectory() );
  		}
  	  }
  	
  	
  

  	/**
  	 * @param sentence
  	 * @return modifiedSentence
  	 * 
  	 * Verbs returned from GF take the form "to be moving"
  	 * this procedure removes the "to be" from the sentence.
  	 */
  	public String removeToBe(String sentence)  {
  		
  		String modifiedSentence = sentence.replaceAll("to be ", "");
  		modifiedSentence = modifiedSentence.replaceAll("to ", "");
  		return modifiedSentence;
  	  }
}
