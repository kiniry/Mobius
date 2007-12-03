//******************************************************************************
/* Copyright (c) 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TopLevel.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package mobius.prover.exec.toplevel;

import java.io.IOException;

import mobius.prover.Prover;
import mobius.prover.exec.AProverException;
import mobius.prover.exec.ITopLevel;
import mobius.prover.exec.toplevel.exceptions.ThreadDeathException;
import mobius.prover.exec.toplevel.exceptions.TimeOutException;
import mobius.prover.exec.toplevel.exceptions.TopLevelDeathException;
import mobius.prover.exec.toplevel.exceptions.ToplevelException;
import mobius.prover.exec.toplevel.stream.IStreamListener;
import mobius.prover.exec.toplevel.stream.InputStreamHandler;
import mobius.prover.exec.toplevel.stream.StreamHandler;
import mobius.prover.plugins.IProverTopLevel;
import mobius.prover.plugins.exceptions.ProverException;



/**
 * Class to manage TopLevel. It is generic for all the provers.
 * It can be subclassed to get more elaborated API (and prover
 * specific), adding new standard commands.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class TopLevel implements ITopLevel {

  /** The Break String: Ctrl-Brk. */
  public static final String BREAKSTR;
  /** The Break character. */
  private static final char BREAK = 3;
  
  static {
    BREAKSTR = "" + BREAK;
  }
  
  
  /** the buffer containing the latest entries from the standard output. */  
  private StringBuffer fStdBuffer = new StringBuffer();
  /** the buffer containing the latest entries from the error output. */
  private StringBuffer fErrBuffer = new StringBuffer();
  /** the current prover instanciated by the top level. */
  private Prover fProver;
  /** the top level translator as specified by the prover. */
  private IProverTopLevel fProverTopLevel;
  

  /** the top level standard input. */
  private InputStreamHandler fIn;
  /** the top level standard output. */
  private StreamHandler fOut;
  /** the top level error output. */
  private StreamHandler fErr;

  /** the top level process. */
  private Process fProverProc;
  /** the grace time. */
  private int fGraceTime;
  /** the command line to call the top level. */
  private String[] fCmds;
  /** tells whether or not the toplevel is alive. */
  private boolean fIsAlive = true;
  /** tells whether or not the toplevel is processing a command. */
  private boolean fIsWorking;
  

  /**
   * Create a new instance of a top level.
   * @param name the language which host the top level
   * @param path the path of the libraries
   * @throws ProverException if something went wrong
   */
  public TopLevel(final String name, 
                  final String[] path) throws ProverException {
    fProver = Prover.get(name);
    if (fProver == null) {
      throw new ProverException("Prover " + name + " not found!");
    }
    fProverTopLevel = fProver.getTopLevelTranslator();
    fCmds = fProverTopLevel.getCommands(fProver.getTop(), path);
    fGraceTime = fProver.getGraceTime();
    startProcess();
  }

  /** {@inheritDoc} */
  @Override
  public void addStandardStreamListener(final IStreamListener isl) {
    fOut.addStreamListener(isl);
  }
  
  /** {@inheritDoc} */
  @Override
  public void removeStandardStreamListener(final IStreamListener isl) {
    fOut.removeStreamListener(isl);
  }
  

  /** {@inheritDoc} */
  @Override
  public void addErrorStreamListener(final IStreamListener ipl) {
    fErr.addStreamListener(ipl);
  }
  
  /** {@inheritDoc} */
  @Override
  public void removeErrorStreamListener(final IStreamListener ipl) {
    fErr.removeStreamListener(ipl);
  }
  
  /**
   * Stop the currently running top level.
   */
  public void dispose() {
    this.stop();
  }
  
  /**
   * Start a new top level process.
   * @throws ProverException If the process could not be started properly.
   */
  private void startProcess()
    throws ProverException {
    fIsWorking = false;
    try {
      fProverProc = Runtime.getRuntime().exec(fCmds);
      
      fOut = StreamHandler.createStreamHandler(fProverProc.getInputStream());
      fErr = StreamHandler.createStreamHandler(fProverProc.getErrorStream());
      fIn = new InputStreamHandler(fProverProc.getOutputStream());
      fIsAlive = true;
    } 
    catch (IOException e) {
      throw new ProverException(
        "Error running command: '" + fCmds[0] + "': " + e.toString());
    }
    if (fProverProc == null) {
      throw new ProverException("TopLevel", "Error running command: " + fCmds[0]); 
    }
    clearBuffer();
  }





  /** {@inheritDoc} */
  @Override
  public void waitForStandardInput() throws ToplevelException {
    final StringBuffer str = new StringBuffer();
    try {
      waitForInput(fOut, str);
      fStdBuffer.append(str);
    }
    catch (IOException e) {
      fIsWorking = false;
      e.printStackTrace();
    }
  }

  /** {@inheritDoc} */
  @Override
  public void waitForErrorInput() throws ToplevelException {
    final StringBuffer str = new StringBuffer();
    try {
      waitForInput(fErr, str);
      fErrBuffer.append(str);
    }
    catch (IOException e) {
      fIsWorking = false;
      e.printStackTrace();
    }
  }
  
  
  /**
   * Wait for the input coming from the specified stream.
   * @param stream the stream to manage
   * @param buff the output buffer
   * @throws IOException In case of a system error on the stream
   * @throws ToplevelException In case of the grace time, 
   * death of the thread, death of the prover
   */
  private void waitForInput(final StreamHandler stream, 
                            final StringBuffer buff) throws IOException, ToplevelException {
    int i;
    try {
      Thread.yield();
      for (i = 0; i < fGraceTime && (!stream.hasFinished()) && isAlive(); i++) {
        stream.getThread().join(1000);
      } 
      if (!stream.hasFinished()) {
        if (!isAlive()) {
          throw new TopLevelDeathException(fProver);
        }
        else if (i == fGraceTime) {
          throw new TimeOutException(fProver);
        }
        else {
          throw new ThreadDeathException(fProver);
        }
      }
    }
    catch (InterruptedException e) {
      e.printStackTrace();
    }
    buff.append(stream.getBuffer());
    //in.fireToListeners();
    stream.clearBuffer();
  }
  

  /**
   * Sends the given command to the prover and waits for input
   * coming from the prover.
   * @param command the command sent to the prover
   * @throws ProverException
   */
  public void sendToProver(final String command) throws ProverException {
    clearBuffer();  
    if (!isAlive()) {
      throw new TopLevelDeathException(fProver);
    }
    if (command.trim().equals("") && 
        !command.equals(BREAKSTR)) {
      return;
    }
    fIsWorking = true;
    fIn.println(command);
    try {
      waitForStandardInput();
      waitForErrorInput();
    } 
    catch (ProverException ec) {
      fIsWorking = false;
      throw ec;
    }
    if (!fIsWorking) {
      throw new ProverException("I was interrupted!");
    }
    fIsWorking = false;
  }

  /**
   * Sends the given command to the prover and waits for input
   * coming from the prover.
   * @param command the command sent to the prover
   * @throws AProverException
   */
  public void sendCommand(final String command) throws AProverException {
//    System.out.println(command);
    fProverTopLevel.sendCommand(this, command);
  }

  
  /**
   * Restart the currently running top level.
   * @throws ProverException If the restart couldn't be done properly.
   */
  public void restart() throws ProverException {
    startProcess();
  }

  /**
   * Tells if the top level is computing something.
   * @return <code>true</code> if the top level is computing.
   */
  public boolean isWorking() {
    return fIsWorking;
  }
  
  /**
   * Tries to undo the last step from the top level,
   * by calling the {@link mobius.prover.plugins.IProverTopLevel#undo(ITopLevel)}.
   * @throws AProverException If there was an error.
   */
  public void undo() throws AProverException {
    fProverTopLevel.undo(this);
  }  

  /** {@inheritDoc} */
  @Override
  public void stop() {
    fProverProc.destroy();
    fIsAlive = false;
    fIsWorking = false;
  }

  /** {@inheritDoc} */
  @Override
  public boolean isAlive() {
    if (fIsAlive) {
      try {    
        fProverProc.exitValue();
        fIsAlive = false;
      } 
      catch (IllegalThreadStateException itse) {
        fIsAlive = true;
      }
    }
    return fIsAlive;
  }
  
  
  /** {@inheritDoc} */
  @Override
  public String getStdBuffer() {
    return fStdBuffer.toString();
  }

  /** {@inheritDoc} */
  @Override
  public String getErrBuffer() {
    return fErrBuffer.toString();
  }
  
  /** {@inheritDoc} */
  @Override
  public void clearBuffer() {
    clearStdBuffer();
    clearErrBuffer();
  }

  /** {@inheritDoc} */
  @Override
  public void clearStdBuffer() {
    fStdBuffer = new StringBuffer();
    fOut.clearBuffer();
  }
  
  /** {@inheritDoc} */
  @Override
  public void clearErrBuffer() {
    fErrBuffer = new StringBuffer();
    fErr.clearBuffer();
  }
  
  

  
  /**
   * Tries to tell coqtop to stop arguing with these commands.
   * @throws ProverException in case of traumas
   */
  public void doBreak() throws ProverException {
    if (!isWorking()) {
      throw new ProverException("There is nothing to break!");
    }
    fIsWorking = false;
    fIn.print(BREAKSTR);
  }
  

}
