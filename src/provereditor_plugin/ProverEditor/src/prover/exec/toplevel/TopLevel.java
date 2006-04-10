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
import prover.exec.toplevel.exceptions.ProverException;
import prover.exec.toplevel.exceptions.ToplevelException;
import prover.exec.toplevel.exceptions.toplevel.ThreadDeathException;
import prover.exec.toplevel.exceptions.toplevel.TimeOutException;
import prover.exec.toplevel.exceptions.toplevel.TopLevelDeathException;
import prover.exec.toplevel.stream.IStreamListener;
import prover.exec.toplevel.stream.InputStreamHandler;
import prover.exec.toplevel.stream.StreamHandler;
import prover.plugins.IProverTopLevel;


/**
 * Class to manage TopLevel
 * @author Julien Charles
 */
public class TopLevel implements ITopLevel {
	private StringBuffer fStdBuffer = new StringBuffer();
	private StringBuffer fErrBuffer = new StringBuffer();
	private Prover fProver;
	private IProverTopLevel fProverTopLevel;
	
	
	private StreamHandler fIn;
	private InputStreamHandler fOut;
	private StreamHandler fErr;

	
	private Process fProverProc;
	private int fiGraceTime;
	private String[] fCmds;
	private boolean fbIsAlive = true;
	private boolean fbIsWorking;
	
//	public final int NORMAL = IStreamListener.NORMAL;
//	public final int ERROR = IStreamListener.ERROR;
	
	private static char BREAK = 3;
	public static String BREAKSTR;
	static {
		BREAKSTR = "" + BREAK;
	}
	
	public void addStreamListener(IStreamListener isl) {
		fIn.addStreamListener(isl);
	}
	public void removeStreamListener(IStreamListener isl) {
		fIn.removeStreamListener(isl);
	}
	
	public void addErrorStreamListener(IStreamListener ipl) {
		fErr.addStreamListener(ipl);
	}
	public void removeErrorStreamListener(IStreamListener ipl) {
		fErr.removeStreamListener(ipl);
	}
	
	public void dispose() {
		this.stop();
	}
	private void startProcess()
		throws ProverException {
		fbIsWorking= false;
		try {
			fProverProc = Runtime.getRuntime().exec(fCmds);
			
			fIn = StreamHandler.createStreamHandler(IStreamListener.NORMAL, fProverProc.getInputStream());
			fErr = StreamHandler.createStreamHandler(IStreamListener.ERROR, fProverProc.getErrorStream());
			fOut = new InputStreamHandler(fProverProc.getOutputStream());
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


	/**
	 * 
	 * @param type One of the values {@link IStreamListener#NORMAL} or 
	 * {@link IStreamListener#ERROR}
	 * @throws ToplevelException if a top level exception was raised
	 */
	public void waitForInput(int type) throws ToplevelException {
		StringBuffer str = new StringBuffer();
		try {
			switch (type) {
				case IStreamListener.NORMAL:
					waitForInput(fIn, str);
					fStdBuffer.append(str);
					break;
				case IStreamListener.ERROR:
					waitForInput(fErr, str);
					fErrBuffer.append(str);
					break;
			}
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
		fOut.println(command);
		try {
				waitForInput(IStreamListener.NORMAL);
				waitForInput(IStreamListener.ERROR);
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


	public void restart() throws ProverException {
		startProcess();
	}


	public void stop() {
		fProverProc.destroy();
		fbIsAlive = false;
		fbIsWorking = false;
	}

	
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
	
	public String getStdBuffer() {
		return fStdBuffer.toString();
	}

	public String getErrBuffer() {
		return fErrBuffer.toString();
	}
	
	public void clearBuffer() {
		clearStdBuffer();
		clearErrBuffer();
	}
	
	public void clearStdBuffer() {
		fStdBuffer = new StringBuffer();
		fErrBuffer = new StringBuffer();
	}
	public void clearErrBuffer() {
		fStdBuffer = new StringBuffer();
		fErrBuffer = new StringBuffer();
	}
	
	public boolean isWorking() {
		return fbIsWorking;
	}
	
	
	/**
	 * Tries to tell coqtop to stop arguing with these @$!%* commands.
	 * @throws ProverException in case of traumas
	 */
	public void doBreak() throws ProverException {
		if(!isWorking())
			throw new ProverException("There is nothing to break!");
		fbIsWorking = false;
		fOut.println(BREAKSTR);
	}
	
	public void undo() throws AProverException {
		fProverTopLevel.undo(this);
	}
}
