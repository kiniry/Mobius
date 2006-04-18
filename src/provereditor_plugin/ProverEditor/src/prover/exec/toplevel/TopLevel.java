//******************************************************************************
/* Copyright (c) 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TopLevel.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package prover.exec.toplevel;

import java.io.IOException;

import prover.Prover;
import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.exec.exceptions.ProverException;
import prover.exec.exceptions.ToplevelException;
import prover.exec.toplevel.exceptions.ThreadDeathException;
import prover.exec.toplevel.exceptions.TimeOutException;
import prover.exec.toplevel.exceptions.TopLevelDeathException;
import prover.exec.toplevel.stream.IStreamListener;
import prover.exec.toplevel.stream.InputStreamHandler;
import prover.exec.toplevel.stream.StreamHandler;
import prover.plugins.IProverTopLevel;


/**
 * Class to manage TopLevel. It is generic for all the provers.
 * It can be subclassed to get more elaborated API (and prover
 * specific), adding new standard commands.
 * @author J. Charles
 */
public class TopLevel implements ITopLevel {
	/** the buffer containing the latest entries from the standard output */	
	private StringBuffer fStdBuffer = new StringBuffer();
	/** the buffer containing the latest entries from the error output */
	private StringBuffer fErrBuffer = new StringBuffer();
	/** the current prover instanciated by the top level */
	private Prover fProver;
	/** the top level translator as specified by the prover */
	private IProverTopLevel fProverTopLevel;
	

	/** the top level standard input */
	private InputStreamHandler fIn;
	/** the top level standard output */
	private StreamHandler fOut;
	/** the top level error output */
	private StreamHandler fErr;

	/** the top level process */
	private Process fProverProc;
	/** the grace time */
	private int fiGraceTime;
	/** the command line to call the top level */
	private String[] fCmds;
	/** tells whether or not the toplevel is alive */
	private boolean fbIsAlive = true;
	/** tells whether or not the toplevel is processing a command */
	private boolean fbIsWorking;
	
	/** The Break character */
	private final static char BREAK = 3;
	/** The Break String: Ctrl-Brk */
	public static String BREAKSTR;
	static {
		BREAKSTR = "" + BREAK;
	}
	
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#addStandardStreamListener(prover.exec.toplevel.stream.IStreamListener)
	 */
	public void addStandardStreamListener(IStreamListener isl) {
		fOut.addStreamListener(isl);
	}
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#removeStandardStreamListener(prover.exec.toplevel.stream.IStreamListener)
	 */
	public void removeStandardStreamListener(IStreamListener isl) {
		fOut.removeStreamListener(isl);
	}
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#addErrorStreamListener(prover.exec.toplevel.stream.IStreamListener)
	 */
	public void addErrorStreamListener(IStreamListener ipl) {
		fErr.addStreamListener(ipl);
	}
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#removeErrorStreamListener(prover.exec.toplevel.stream.IStreamListener)
	 */
	public void removeErrorStreamListener(IStreamListener ipl) {
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
		fbIsWorking= false;
		try {
			fProverProc = Runtime.getRuntime().exec(fCmds);
			
			fOut = StreamHandler.createStreamHandler(fProverProc.getInputStream());
			fErr = StreamHandler.createStreamHandler(fProverProc.getErrorStream());
			fIn = new InputStreamHandler(fProverProc.getOutputStream());
			fbIsAlive = true;
		} catch (IOException e) {
			throw new ProverException(
				"Error running command: '" + fCmds[0] + "': " + e.toString());
		}
		if (fProverProc == null) {
			throw new ProverException("TopLevel", "Error running command: " + fCmds[0]); 
		}
		clearBuffer();
	}

	/**
	 * Create a new instance of a top level.
	 * @param name the language which host the top level
	 * @param path the path of the libraries
	 * @throws ProverException if something went wrong
	 */
	public TopLevel(String name, String[] path) throws ProverException {
		fProver = Prover.get(name);
		if(fProver == null) {
			throw new ProverException("Prover " + name + " not found!");
		}
		fProverTopLevel = fProver.getTopLevelTranslator();
		fCmds = fProverTopLevel.getCommands(fProver.getTop(), path);
		int iGrace = fProver.getGraceTime();
		fiGraceTime = iGrace == 0 ? 123456 : iGrace;
		
		startProcess();
	}


	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#waitForStandardInput()
	 */
	public void waitForStandardInput() throws ToplevelException {
		StringBuffer str = new StringBuffer();
		try {
			waitForInput(fOut, str);
			fStdBuffer.append(str);
		}
		catch (IOException e) {
			fbIsWorking = false;
			e.printStackTrace();
		}
	}
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#waitForErrorInput()
	 */
	public void waitForErrorInput() throws ToplevelException {
		StringBuffer str = new StringBuffer();
		try {
			waitForInput(fErr, str);
			fErrBuffer.append(str);
		}
		catch (IOException e) {
			fbIsWorking = false;
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
	private void waitForInput(StreamHandler stream, StringBuffer buff) throws IOException, ToplevelException {
		int i;
		try {
			Thread.yield();
			for (i = 0; i < fiGraceTime && (!stream.hasFinished()) && isAlive(); i++) {
				stream.getThread().join(1000);
			} 
			if (!stream.hasFinished()) {
				if (!isAlive())
					throw new TopLevelDeathException(fProver);
				else if(i== fiGraceTime)
					throw new TimeOutException(fProver);
				else
					throw new ThreadDeathException(fProver);
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
	 * coming from the,
	 */
	public void sendToProver(String command) throws ProverException {
		clearBuffer();	
		if(!isAlive()) {
			throw new TopLevelDeathException(fProver);
		}
		if (command.trim().equals("") && !command.equals(BREAKSTR))
			return;
		fbIsWorking = true;
		fIn.println(command);
		try {
				waitForStandardInput();
				waitForErrorInput();
		} 
		catch (ProverException ec) {
			fbIsWorking = false;
			throw ec;
		}
		if(!fbIsWorking)
			throw new ProverException("I was interrupted!");
		fbIsWorking = false;
	}

	/**
	 * Sends the given command to the prover and waits for input
	 * coming from the,
	 */
	public void sendCommand(String command) throws AProverException {
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
		return fbIsWorking;
	}
	
	/**
	 * Tries to undo the last step from the top level,
	 * by calling the {@link prover.plugins.IProverTopLevel#undo(ITopLevel)}.
	 * @throws AProverException If there was an error.
	 */
	public void undo() throws AProverException {
		fProverTopLevel.undo(this);
	}	
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#stop()
	 */
	public void stop() {
		fProverProc.destroy();
		fbIsAlive = false;
		fbIsWorking = false;
	}

	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#isAlive()
	 */
	public boolean isAlive() {
		if (fbIsAlive) {
			try {
				fProverProc.exitValue();
				return false;
			} catch (IllegalThreadStateException itse) {
				return true;
			}
		}
		else return false;
	}
	
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#getStdBuffer()
	 */
	public String getStdBuffer() {
		return fStdBuffer.toString();
	}

	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#getErrBuffer()
	 */
	public String getErrBuffer() {
		return fErrBuffer.toString();
	}
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#clearBuffer()
	 */
	public void clearBuffer() {
		clearStdBuffer();
		clearErrBuffer();
	}
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#clearStdBuffer()
	 */
	public void clearStdBuffer() {
		fStdBuffer = new StringBuffer();
		fErrBuffer = new StringBuffer();
	}
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.ITopLevel#clearErrBuffer()
	 */
	public void clearErrBuffer() {
		fStdBuffer = new StringBuffer();
		fErrBuffer = new StringBuffer();
	}
	
	

	
	/**
	 * Tries to tell coqtop to stop arguing with these commands.
	 * @throws ProverException in case of traumas
	 */
	public void doBreak() throws ProverException {
		if(!isWorking())
			throw new ProverException("There is nothing to break!");
		fbIsWorking = false;
		fIn.print(BREAKSTR);
	}
	

}
