//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Simplify.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package simplifyPlugin;

import jack.util.Logger;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;

/**
 * Example class allowing using the simplify prover from Java.
 * @author A. Requet L. Burdy
 */
public class Simplify {
	private static final boolean echo = false;

	/**
	 * PrintStream used to send commands to the simplify process.
	 */
	private PrintStream input;

	/**
	 * The simplify process.
	 */
	private Process simplify;

	//@ invariant (simplify == null) <==> (input == null);

	private void startProcess(String cmd, String param)
		throws SimplifyException {
		String[] cmds = { cmd.trim(), "-nosc", param };
		try {
			simplify = Runtime.getRuntime().exec(cmds);
		} catch (IOException e) {
			throw new SimplifyException(
				"Error running command: " + cmd + ": " + e.toString());
		}

		if (simplify == null) {
			throw new SimplifyException(Messages.getString("Simplify.Error_running_command___4") + cmd); //$NON-NLS-1$
		}
	}

	/**
	 * Creates a new Simplify prover interface.
	 */
	public Simplify(String cmd, String param) throws SimplifyException {
		startProcess(cmd, param);
	}

	/**
	 * Eat characters until the command prompt is reached, and stores the output
	 * from Simplify into <code>buff</code>.
	 */
	private void waitForPrompt(StringBuffer buff)
		throws IOException, SimplifyException {
		int b;
		boolean got_gt = false;

		InputStream s = simplify.getInputStream();
		do {
			b = s.read();

			switch (b) {
				case '>' :
					got_gt = true;
					break;
				case '\t' :
					if (got_gt == true) {
						return;
					}
					break;
				case -1 :
					throw new SimplifyException(Messages.getString("Simplify.Prover_Terminated_5")); //$NON-NLS-1$
				default :
					got_gt = false;
					buff.append((char) b);
					if (echo) {
						Logger.get().print((char) b);
					}
			}

		} while (true);
	}

	/**
	 * Eat characters until the command prompt is reached.
	 */
	public void waitForPrompt() throws SimplifyException {
		int b;
		boolean got_gt = false;
		// get the process output stream 
		InputStream s = simplify.getInputStream();

		do {
			try {
				b = s.read();
			} catch (IOException e) {
				Logger.err.println(Messages.getString("Simplify.IOException_catched____6") + e.toString()); //$NON-NLS-1$
				return;
			}
			switch (b) {
				case '>' :
					got_gt = true;
					break;
				case '\t' :
					if (got_gt == true) {
						return;
					}
					break;
				case -1 :
					// prover terminated
					throw new SimplifyException(Messages.getString("Simplify.Prover_terminated_7")); //$NON-NLS-1$
				default :
					got_gt = false;
					if (echo) {
						Logger.get().print((char) b);
					}
			}

		} while (true);
	}

	/**
	 * Eat prompt characters.
	 */
	public int eatPrompt() throws SimplifyException {
		int b;
		boolean got_gt = false;
		// get the process output stream 
		InputStream s = simplify.getInputStream();

		do {
			try {
				b = s.read();
			} catch (IOException e) {
				Logger.err.println(Messages.getString("Simplify.IOException_catched____8") + e.toString()); //$NON-NLS-1$
				return 0;
			}
			switch (b) {
				//				case 'W' : // Warning:
				//					StringBuffer output = new StringBuffer();
				//					try {
				//						waitForPrompt(output);
				//					} catch (IOException e) {
				//						throw new SimplifyException(
				//							"IOException catched : " + e.toString());
				//					}
				//					try {
				//						return s.read();
				//					} catch (IOException e) {
				//						Logger.err.println(
				//							"IOException catched : " + e.toString());
				//						return 0;
				//					}
				case '>' :
					got_gt = true;
					break;
				case '\t' :
					if (got_gt == true) {
						break;
					}
					return b;
				case -1 :
					// prover terminated
					throw new SimplifyException(Messages.getString("Simplify.Prover_terminated_9")); //$NON-NLS-1$
				default :
					return b;
			}

		} while (true);
	}

	/**
	 * Sends the given command to the prover and waits for the prompt,
	 * printing all the output of the prover to the standard output.
	 */
	public void sendCommand(String command) throws SimplifyException {
		input.println(command);
		input.flush();
		if (echo) {
			Logger.get().println(Messages.getString("Simplify.Sending_command___10")); //$NON-NLS-1$
			Logger.get().println(command);
		}
		waitForPrompt();
	}

	/**
	 * Helper method used by prove for throwing exceptions. It throws a
	 * ProverException containing the output from simplify.
	 * <p>
	 * Note that the ProverException can contain the text of an IOException
	 * if such an exception is thrown by the stream read.
	 */
	//@ ensures false;
	//@ exsures (ProverException e) true;
	private void proveThrowException(int first_char, String message)
		throws SimplifyException {
		StringBuffer output = new StringBuffer();
		if (message != null) {
			output.append(message);
		}
		output.append((char) first_char);
		try {
			waitForPrompt(output);
		} catch (IOException e) {
			throw new SimplifyException(
				Messages.getString("Simplify.IOException_catched____11") + e.toString()); //$NON-NLS-1$
		}
		throw new SimplifyException(output.toString());
	}

	/**
	 * Try to prove the given formula.
	 * <p>
	 * @return true if the formula is correct, false if it could not be
	 *   proved.
	 */
	public boolean prove() throws SimplifyException {
		int first_char = 0;

		while (true) {
			first_char = eatPrompt(); //simplify.getInputStream().read();

			switch (first_char) {
				case 'W' : // Warning:
					StringBuffer output = new StringBuffer(first_char);
					try {
						waitForPrompt(output);
					} catch (IOException e) {
						throw new SimplifyException(
							Messages.getString("Simplify.IOException_catched____12") + e.toString()); //$NON-NLS-1$
					}
					if (output.indexOf("Valid") == output.length() - 8)
						return true;
					else if (output.indexOf("Invalid") == output.length() - 10)
						return false;
					break;
				case 'B' : // Bad input:
					proveThrowException(first_char, null);
					// never reach this point
					return false;
				case 'C' : // Counterexample:
					waitForPrompt();
					return false;
					// x: Valid
				case '1' :
				case '2' :
				case '3' :
				case '4' :
				case '5' :
				case '6' :
				case '7' :
				case '8' :
				case '9' :
					// wait for the command prompt
					waitForPrompt();
					return true;
				default :
					// should never happen
					proveThrowException(
						first_char,
						Messages.getString("Simplify.Unexpected_output_from_simplify___15")); //$NON-NLS-1$
					return false;
			}
		}
	}

	/**
	 * Push the given backgroud predicate.
	 * This is equivalent to sending the commant
	 * <code>(BG_PUSH bg )</code> to simplify.
	 */
	public void pushBg(String bg) throws SimplifyException {
		input.print("(BG_PUSH ");
		input.print(bg);
		input.println(")");
		input.flush();
		if (echo) {
			Logger.get().println(Messages.getString("Simplify.Sending_background_predicate___18")); //$NON-NLS-1$
			Logger.get().println(bg);
		}
		waitForPrompt();
	}

	/**
	 * Pop the last background predicate pushed.
	 * This method is equivalent to a call to 
	 * <code>sendCommand("(BG_POP)")</code>
	 */
	public void popBg() throws SimplifyException {
		sendCommand("(BG_POP)");
		// do not wait for prompt, since sendCommand already does
	}

	/**
	 * Stop the simplify process.
	 */
	public void stop() {
		simplify.destroy();
		try {
			simplify.waitFor();
		} catch (InterruptedException e) {
			Logger.err.println(
				Messages.getString("Simplify.InterruptedException_catched____20") + e.toString()); //$NON-NLS-1$
		}
		input = null;
		simplify = null;
	}

	//	/**
	//	 * Call prove with the given formula, and check that it returns the 
	//	 * expected result.
	//	 * <p>
	//	 * Print information on stderr.
	//	 * 
	//	 * @return true if the proof result is the expected one, false otherwise.
	//	 */
	//	public boolean testProof(String formula, boolean expected) {
	//		try {
	//			boolean result = prove(formula);
	//			if (result == expected) {
	//				Logger.err.println(
	//					"OK: " + formula + " = " + expected + ", as expected");
	//				return true;
	//			} else {
	//				Logger.err.println(
	//					"**ERROR: "
	//						+ formula
	//						+ " = "
	//						+ result
	//						+ ", expected "
	//						+ expected);
	//				return false;
	//			}
	//		} catch (SimplifyException e) {
	//			Logger.err.println("**EXCEPTION: " + formula + ": " + e.toString());
	//			return false;
	//		}
	//	}

	/**
	 * Check that the given command raise an exception.
	 * 
	 * @return true if the command raised an exception, false otherwise.
	 */
	boolean checkException() {
		try {
			boolean res = prove();
			Logger.err.println(Messages.getString("Simplify.ERROR__expected_exception,_got__21") + res); //$NON-NLS-1$
			return false;
		} catch (SimplifyException e) {
			Logger.err.println(Messages.getString("Simplify.OK__catched_exception__22") + e.toString()); //$NON-NLS-1$
		}
		return true;
	}

	/**
	 * @return
	 */
	public PrintStream getInput() {
		return input;
	}

	/**
	 * @return
	 */
	public Process getSimplify() {
		return simplify;
	}

	public boolean isAlive() {
		try {
			simplify.exitValue();
			return false;
		} catch (IllegalThreadStateException itse) {
			return true;
		}
	}

	/**
	 * @param stream
	 */
	public void setInput(PrintStream stream) {
		input = stream;
	}

}
