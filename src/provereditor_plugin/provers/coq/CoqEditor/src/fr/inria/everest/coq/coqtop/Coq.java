//******************************************************************************
/* Copyright (c) 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Coq.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package fr.inria.everest.coq.coqtop;

import java.io.IOException;

import prover.exec.AProverException;
import prover.exec.IStreamListener;
import prover.exec.ITopLevel;
import prover.exec.toplevel.exceptions.CoqException;
import prover.exec.toplevel.exceptions.CoqTopException;
import prover.exec.toplevel.stream.ErrorStreamHandler;
import prover.exec.toplevel.stream.InputStreamHandler;
import prover.exec.toplevel.stream.StandardStreamHandler;


/**
 * Class to manage Coq
 * @author Julien Charles
 */
public class Coq implements ITopLevel {
	private StringBuffer coqBuffer = new StringBuffer();
	
	private StandardStreamHandler in;
	private InputStreamHandler out;
	private ErrorStreamHandler err;

	
	private Process coq;
	private int iGraceTime;
	private String[] cmds;
	private boolean bIsAlive = true;
	private Thread tin;
	private String prompt;
	private int iStep;
	private int iProofStep;

	private int iIsWorking = 0;
	
	private static char BREAK = 3;
	public static String BREAKSTR;
	static {
		BREAKSTR = "" + BREAK;
	}
	
	public void addListener(IStreamListener isl) {
		in.addStreamListener(isl);
	}
	public void removeListener(IStreamListener isl) {
		in.removeStreamListener(isl);
	}
	public void dispose() {
		this.stop();
	}
	private void startProcess()
		throws CoqException {
		iIsWorking= 1;
		try {
			coq = Runtime.getRuntime().exec(cmds);
			
			in = new StandardStreamHandler(coq.getInputStream());
			tin = new Thread(in);
			tin.start();
			err = new ErrorStreamHandler(coq.getErrorStream());
			out = new InputStreamHandler(coq.getOutputStream());
			bIsAlive = true;
		} catch (IOException e) {
			throw new CoqException(
				"Error running command: '" + cmds[0] + "': " + e.toString());
		}
		
		if (coq == null) {
			throw new CoqException("Coq.Error_running_command___4" + cmds[0]); //$NON-NLS-1$
		}
		clearBuffer();
		try {
			waitForPrompt(coqBuffer);
		} catch (CoqTopException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}


	public Coq(String cmd, String[] path, int iGrace) throws CoqException {
		if(path != null) {
			cmds = new String[2 + path.length * 2];
			for(int i = 0; i < path.length; i++) {
				cmds[(2 * i) + 1] = "-I";
				cmds[(2 * i) + 2] = path[i];
			}
			
		}
		else {
			cmds = new String[2];
		}
		cmds[0] = cmd.trim();
		cmds[cmds.length - 1] = "-emacs";
		iGraceTime = iGrace == 0 ? 123456 : iGrace;
		
		startProcess();
	}

	
	private synchronized void waitForPrompt(StringBuffer buff)
		throws IOException, CoqTopException {
		
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
				throw new CoqTopException("Oh no ! Coq was killed !");
			}
			if (err.isStillEating()) {
				err.stopEating();
				if(i== iGraceTime)
					throw new CoqTopException("Timed out !"); //ca me gave!
				else
					throw new CoqTopException("Unexpected thread death !");
			}
			err.stopEating();
			do {
				Thread.yield();
				newPrompt = err.getPrompt();
				if(!(bIsAlive && iIsWorking > 0))
					return;
			} while(newPrompt.equals("")) ;
			prompt = newPrompt;
			//System.out.println(prompt);
			String [] tab = prompt.split("<");
			if(tab.length > 1) {
				String [] nums = tab[1].split("\\|");
				iStep = Integer.valueOf(nums[0].trim()).intValue();
				iProofStep = Integer.valueOf(nums[nums.length - 1].trim()).intValue();
				//if(!nums[1].trim().equals("")) {
				//	;
				//}
				//System.err.println(nums.length + " " + iProofStep);
			}
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}

	protected void waitForMoreInput() throws IOException, CoqTopException {
		waitForMoreInput(coqBuffer);
	}
	
	private synchronized void waitForMoreInput(StringBuffer buff) throws IOException, CoqTopException {
		
		int i;
		try {
			Thread.yield();
			for (i = 0; i < iGraceTime && (!in.hasFinished()) && isAlive(); i++) {
				tin.join(100);
			} 
			if (!in.hasFinished()) {
				if (!isAlive())
					throw new CoqTopException("Oh no ! Coq was killed !");
				else if(i== iGraceTime)
					throw new CoqTopException("Timed out !"); //ca me gave!
				else
					throw new CoqTopException("Unexpected thread death !");
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
	public void sendCommand(String command) throws CoqException {

		clearBuffer();
		if(!isAlive()) {
			/*
			 * throw new CoqTopException("Maldoror is dead dead dead!!!");
			 * soyons un peu serieux...
			 */
			throw new CoqTopException("Coqtop has been killed.");
		}
		if (command.trim().equals("") && !command.equals(BREAKSTR))
			return;

		if(iIsWorking < 0) iIsWorking = 0;
		iIsWorking++;
		
		out.println(command);
		if(command.split("\\(\\*").length > command.split("\\*\\)").length)
			return;
		StringBuffer str = new StringBuffer();
		try {
				waitForPrompt(str);
				//if(command.startsWith("Proof"))
				waitForMoreInput(str);
		} catch (IOException e) {
			iIsWorking = 0;
			e.printStackTrace();
		}
		catch (CoqException ec) {
			iIsWorking --;
			throw ec;
		}
		coqBuffer.append(str);
		if(iIsWorking == 0)
			throw new CoqException("I was interrupted!");
		iIsWorking--;
	}

	public String getPrompt() {
		return prompt;
	}

	public void restart() throws CoqException {
		startProcess();
	}


	public void stop() {
		coq.destroy();
		//try {
		bIsAlive = false;
		iIsWorking = 0;
			// it is normally already terminated... coq.waitFor();
		//} catch (InterruptedException e) {
		//	System.err.println(
		//		"Coq.InterruptedException_catched____20" + e.toString()); //$NON-NLS-1$
		//}
	}


	public boolean isProofMode() {
		return !prompt.startsWith("Coq <");
	}
	
	public boolean isAlive() {
		if (bIsAlive) {
			try {
				coq.exitValue();
				return false;
			} catch (IllegalThreadStateException itse) {
				return true;
			}
		}
		else return false;
	}
	
	public String getBuffer() {
		return coqBuffer.toString();
	}
	
	public void clearBuffer() {
		coqBuffer = new StringBuffer();
	}
	
	public int getStep() {
		return iStep;
	}
	public int getProofStep() {
		return iProofStep;
	}
	
	public boolean isWorking() {
		return iIsWorking >0;
	}
	
	
	/**
	 * Tries to tell coqtop to stop arguing with these @$!%* commands.
	 * @throws CoqException in case of traumas
	 */
	public void doBreak() throws CoqException {
		if(!isWorking())
			throw new CoqException("There is nothing to break!");
		iIsWorking --;
		if(iIsWorking < 0) iIsWorking = 0;
		out.println(BREAKSTR);
	}
	public ITopLevel createTopLevel(String strCoqTop, String[] path) throws AProverException {
		// TODO Auto-generated method stub
		return null;
	}
	public void undo(int steps) throws AProverException {
		// TODO Auto-generated method stub
		
	}	
}
