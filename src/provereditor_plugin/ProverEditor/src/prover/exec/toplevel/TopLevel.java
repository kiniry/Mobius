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
import prover.exec.ITopLevel;
import prover.exec.toplevel.exceptions.ProverException;
import prover.exec.toplevel.exceptions.ToplevelException;
import prover.exec.toplevel.stream.IStreamListener;
import prover.exec.toplevel.stream.InputStreamHandler;
import prover.exec.toplevel.stream.StreamHandler;


/**
 * Class to manage TopLevel
 * @author Julien Charles
 */
public abstract class TopLevel implements ITopLevel {
	private StringBuffer proverBuffer = new StringBuffer();
	private StringBuffer prompt = new StringBuffer();
	private Prover pkind;
	
	private StreamHandler in;
	private InputStreamHandler out;
	private StreamHandler err;

	
	private Process prover;
	private int iGraceTime;
	private String[] cmds;
	private boolean bIsAlive = true;
	private Thread tin;
	private Thread terr;
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
	
	public void addErrorStreamListener(IStreamListener ipl) {
		err.addStreamListener(ipl);
	}
	public void removeErrorStreamListener(IStreamListener ipl) {
		err.removeStreamListener(ipl);
	}
	
	public void dispose() {
		this.stop();
	}
	private void startProcess()
		throws ProverException {
		iIsWorking= 1;
		try {
			prover = Runtime.getRuntime().exec(cmds);
			
			in = new StreamHandler(IStreamListener.NORMAL, prover.getInputStream());
			err = new StreamHandler(IStreamListener.ERROR, prover.getErrorStream());

			tin = new Thread(in);
			tin.start();
	
			terr = new Thread(err);
			terr.start();
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


	private void waitForPrompt(StringBuffer buff, StringBuffer bufferr)
		throws IOException, ToplevelException {
		waitForMoreInput(in, tin, buff);
		waitForMoreInput(err, terr, bufferr);
//		// on mange le prompt;
//		Thread t;
//		
//		//String strPrompt = prompt;
//		String newPrompt;
//		try {
//			int i = 0;
//			t = new Thread(err);
//			in.hasFinished()
//			t.start();
//			for (i = 0; i < iGraceTime && err.isStillEating() && isAlive(); i++) {
//				t.join(100);
//			}
//				
//			if(!bIsAlive) {
//				err.stopEating();
//				throw new ToplevelException(pkind, "Oh no ! TopLevel was killed !");
//			}
//			if (err.isStillEating()) {
//				err.stopEating();
//				if(i== iGraceTime)
//					throw new ToplevelException(pkind, "Timed out !"); //ca me gave!
//				else
//					throw new ToplevelException(pkind, "Unexpected thread death !");
//			}
//			err.stopEating();
//			do {
//				Thread.yield();
//				newPrompt = err.getPrompt();
//				if(!(bIsAlive && iIsWorking > 0))
//					return;
//			} while(newPrompt.equals("")) ;
//			prompt = newPrompt;
//		} catch (InterruptedException e) {
//			e.printStackTrace();
//		}
	}

//	protected void waitForMoreInput() throws IOException, ToplevelException {
//		waitForMoreInput(proverBuffer);
//	}
	
	
	
	private void waitForMoreInput(StreamHandler in, Thread tin, StringBuffer buff) throws IOException, ToplevelException {
		
		int i;
		try {
			Thread.yield();
			for (i = 0; i < iGraceTime && (!in.hasFinished()) && isAlive(); i++) {
				tin.join(1000);
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

		StringBuffer str1 = new StringBuffer();
		StringBuffer str2 = new StringBuffer();
		try {
				waitForPrompt(str1, str2);
//				waitForMoreInput(str);
		} catch (IOException e) {
			iIsWorking = 0;
			e.printStackTrace();
		}
		catch (ProverException ec) {
			iIsWorking --;
			throw ec;
		}
		proverBuffer.append(str1);
		prompt.append(str2);
		if(iIsWorking == 0)
			throw new ProverException("I was interrupted!");
		iIsWorking--;
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

	public String getPrompt() {
		return prompt.toString();
	}
	
	public void clearBuffer() {
		proverBuffer = new StringBuffer();
		prompt = new StringBuffer();
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
