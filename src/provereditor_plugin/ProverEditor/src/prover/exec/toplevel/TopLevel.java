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
import java.util.HashSet;
import java.util.Iterator;

import prover.Prover;
import prover.exec.ITopLevel;
import prover.exec.toplevel.exceptions.ProverException;
import prover.exec.toplevel.exceptions.ToplevelException;
import prover.exec.toplevel.stream.ErrorStreamHandler;
import prover.exec.toplevel.stream.IStreamListener;
import prover.exec.toplevel.stream.InputStreamHandler;
import prover.exec.toplevel.stream.StandardStreamHandler;


/**
 * Class to manage TopLevel
 * @author Julien Charles
 */
public abstract class TopLevel implements ITopLevel {
	private StringBuffer proverBuffer = new StringBuffer();
	private Prover pkind;
	
	private StandardStreamHandler in;
	private InputStreamHandler out;
	private ErrorStreamHandler err;

	
	private Process prover;
	private int iGraceTime;
	private String[] cmds;
	private boolean bIsAlive = true;
	private Thread tin;
	private String prompt;
	private int iIsWorking = 0;
	
	private static char BREAK = 3;
	public static String BREAKSTR;
	static {
		BREAKSTR = "" + BREAK;
	}
	
	public void addStreamListener(IStreamListener isl) {
		in.addStreamListener(isl);
	}
	public void removeStreamListener(IStreamListener isl) {
		in.removeStreamListener(isl);
	}
	
	HashSet hs = new HashSet();
	public void addPromptListener(IPromptListener ipl) {
		hs.add(ipl);
	}
	public void removePromptListener(IPromptListener ipl) {
		hs.remove(ipl);
	}
	private void firePromptChangeEvent() {
		Iterator iter = hs.iterator();
		while(iter.hasNext()) {
			IPromptListener ipl = (IPromptListener)iter.next();
			ipl.promptHasChanged(this);
		}
	}
	
	public void dispose() {
		this.stop();
	}
	private void startProcess()
		throws ProverException {
		iIsWorking= 1;
		try {
			prover = Runtime.getRuntime().exec(cmds);
			
			in = new StandardStreamHandler(prover.getInputStream());
			tin = new Thread(in);
			tin.start();
			err = new ErrorStreamHandler(prover.getErrorStream());
			out = new InputStreamHandler(prover.getOutputStream());
			bIsAlive = true;
		} catch (IOException e) {
			throw new ProverException(
				"Error running command: '" + cmds[0] + "': " + e.toString());
		}
		
		if (prover == null) {
			throw new ProverException("TopLevel", "Error running command: " + cmds[0]); //$NON-NLS-1$
		}
		clearBuffer();
		try {
			waitForPrompt(proverBuffer);
		} catch (ToplevelException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}


	protected TopLevel(String name, String [] cmd, int iGrace) throws ProverException {
		pkind = Prover.get(name);
		if(pkind == null) {
			throw new ProverException("Prover " + name + " not found!");
		}
		this.cmds = cmd;
		iGraceTime = iGrace == 0 ? 123456 : iGrace;
		
		startProcess();
	}


	private synchronized void waitForPrompt(StringBuffer buff)
		throws IOException, ToplevelException {
		
		// on mange le prompt;
		Thread t;
		
		//String strPrompt = prompt;
		String newPrompt;
		try {
			int i = 0;
			t = new Thread(err);	
			t.start();
			for (i = 0; i < iGraceTime && err.isStillEating() && isAlive(); i++) {
				t.join(100);
			}
				
			if(!bIsAlive) {
				err.stopEating();
				throw new ToplevelException(pkind, "Oh no ! TopLevel was killed !");
			}
			if (err.isStillEating()) {
				err.stopEating();
				if(i== iGraceTime)
					throw new ToplevelException(pkind, "Timed out !"); //ca me gave!
				else
					throw new ToplevelException(pkind, "Unexpected thread death !");
			}
			err.stopEating();
			do {
				Thread.yield();
				newPrompt = err.getPrompt();
				if(!(bIsAlive && iIsWorking > 0))
					return;
			} while(newPrompt.equals("")) ;
			prompt = newPrompt;
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		firePromptChangeEvent();
	}

	protected void waitForMoreInput() throws IOException, ToplevelException {
		waitForMoreInput(proverBuffer);
	}
	
	
	
	private synchronized void waitForMoreInput(StringBuffer buff) throws IOException, ToplevelException {
		
		int i;
		try {
			Thread.yield();
			for (i = 0; i < iGraceTime && (!in.hasFinished()) && isAlive(); i++) {
				tin.join(100);
			} 
			if (!in.hasFinished()) {
				if (!isAlive())
					throw new ToplevelException(pkind, "Oh no ! TopLevel was killed !");
				else if(i== iGraceTime)
					throw new ToplevelException(pkind, "Timed out !"); //ca me gave!
				else
					throw new ToplevelException(pkind, "Unexpected thread death !");
			}
		}
		catch (InterruptedException e) {
			e.printStackTrace();
		}
		buff.append(in.getBuffer());
		//in.fireToListeners();
		in.clearBuffer();
	}
	



	/**
	 * Sends the given command to the prover and waits for the prompt,
	 * printing all the output of the prover to the standard output.
	 */
	public void sendCommand(String command) throws ProverException {

		clearBuffer();
		if(!isAlive()) {
			/*
			 * throw new CoqTopException("Maldoror is dead dead dead!!!");
			 * soyons un peu serieux...
			 */
			throw new ToplevelException(pkind, "The toplevel has been killed.");
		}
		if (command.trim().equals("") && !command.equals(BREAKSTR))
			return;

		if(iIsWorking < 0) iIsWorking = 0;
		iIsWorking++;
		
		out.println(command);

		StringBuffer str = new StringBuffer();
		try {
				waitForPrompt(str);
				waitForMoreInput(str);
		} catch (IOException e) {
			iIsWorking = 0;
			e.printStackTrace();
		}
		catch (ProverException ec) {
			iIsWorking --;
			throw ec;
		}
		proverBuffer.append(str);
		if(iIsWorking == 0)
			throw new ProverException("I was interrupted!");
		iIsWorking--;
	}

	public String getPrompt() {
		return prompt;
	}

	public void restart() throws ProverException {
		startProcess();
	}


	public void stop() {
		prover.destroy();
		bIsAlive = false;
		iIsWorking = 0;
	}

	
	public boolean isAlive() {
		if (bIsAlive) {
			try {
				prover.exitValue();
				return false;
			} catch (IllegalThreadStateException itse) {
				return true;
			}
		}
		else return false;
	}
	
	public String getBuffer() {
		return proverBuffer.toString();
	}
	
	public void clearBuffer() {
		proverBuffer = new StringBuffer();
	}

	
	public boolean isWorking() {
		return iIsWorking >0;
	}
	
	
	/**
	 * Tries to tell coqtop to stop arguing with these @$!%* commands.
	 * @throws ProverException in case of traumas
	 */
	public void doBreak() throws ProverException {
		if(!isWorking())
			throw new ProverException("There is nothing to break!");
		iIsWorking --;
		if(iIsWorking < 0) iIsWorking = 0;
		out.println(BREAKSTR);
	}
}
