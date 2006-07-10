//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: AtelierBProofTask.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package bPlugin;

import jack.plugin.JpovUtil;
import jack.plugin.edit.EditedFile;
import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;
import jack.util.Logger;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.rmi.RemoteException;

import jpov.JpoFile;
import jpov.structure.Class;
import jpov.structure.Goal;
import jpov.structure.JmlFile;
import jpov.structure.Lemma;
import jpov.structure.Proofs;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

import pmi.PmiLexer;
import pmi.PmiParser;
import pmi.PmiParserTokenTypes;
import antlr.collections.AST;

/**
 * ProofTask performing proofs using the AtelierB prover.
 * @author Antoine Requet <antoine.requet@gemplus.com>
 */
public class AtelierBProofTask extends ProofTask {

	/**
	 * Parses a proof script
	 * @param tree The current AST tree
	 * @param stack An already parsed string to concat at the end of the new
	 * parsed.
	 * @return the parsed proof script
	 **/
	private static String parseProofScript(AST tree, String stack) {
		String res = "";
		while (tree != null) {
			if (tree.getType() == PmiParserTokenTypes.B_CURLYOPEN
				|| tree.getType() == PmiParserTokenTypes.B_FORALL
				|| tree.getType() == PmiParserTokenTypes.B_EXISTS
				|| tree.getType() == PmiParserTokenTypes.LITERAL_bool) {
				res += tree.getText()
					+ parseProofScript(tree.getFirstChild(), " ")
					+ stack;
			} else if (tree.getFirstChild() != null) {
				res
					+= parseProofScript(
						tree.getFirstChild(),
						" " + tree.getText())
					+ stack;
			} else
				res += " " + tree.getText() + stack;
			stack = "";
			tree = tree.getNextSibling();
		}
		return res;
	}

	AbServer ab;
	
	ProverBStatus[] pbsa;

	public AtelierBProofTask() {
	}

	/**
	 * Creates a ProofTask using the AtelierB prover for proving the
	 * given jpo file.
	 * @param jpo_file the jpo file that should be proved.
	 */
	public AtelierBProofTask(IFile jpo_file, ICompilationUnit c) {
		super(jpo_file, c);
	}

	/**
	 * Creates a ProofTask using the AtelierB prover for proving the 
	 * given jpo file.
	 * @param jpov the jpo file that should be proved.
	 */
	public AtelierBProofTask(JpoFile jpov) {
		super(jpov);
	}

	public ProofTask factory(IFile jpo_file, ICompilationUnit c) {
		return new AtelierBProofTask(jpo_file, c);
	}

	/**
	 * @see ProofTask#endProof()
	 */
	protected void endProof() {
		// updates status
		try {
			setStatus(importPmi(ab));
		} catch (RemoteException e) {
			setError(AbServer.getErrorReason(e), AbServer.getErrorDetails(e));
		}
		// calls the super method.
		super.endProof();
	}

	/**
	 * @see ProofTask#run()
	 */
	public void run() {
		int current = 0;
		int currentProved = 0;
		try {
			// load the jpov from the file if needed.
			if (jpov == null) {
				startLoad();
				changed();
				try {
					jpov = JpovUtil.loadJpoFile(new EditedFile(jpoFile));
					printPmi(
						jpov.getName(),
						jpov.getJmlFile(),
						jpov.getDirectory());
					ab = AbServer.connect(jpoFile, jpov);
				} catch (Exception e) {
					setError(
						"Error loading file",
						"Exception catched: " + e.toString());
					changed();
					return;

				}
				// the file object is not needed anymore
				jpoFile = null;

				Class[] c = jpov.getJmlFile().getClasses();
				for (int i = 0; i < c.length; i++) c[i].selectAll();

				updateFromJpov();
				changed();
			}

			startProof();
			changed();

			try {
				if (ab.prove(jpov.getName(), jpov.getDirectory(), 0)) {
					while (ab.getProofRunning()) {
						// sleeps for a while
						try {
							sleep(100);
						} catch (InterruptedException e) {
						}

						if (shouldStop) {
							proofAborted();
							// abort if asked to.
							return;
						}

						// checks wether a proof has finished
						int proved = ab.getCptProvedRunning();
						int unproved = ab.getCptUnprovedRunning();

						if (current < proved + unproved) {
							// updates statistics
							increaseTried((proved + unproved) - current);
							increaseProved(proved - currentProved);
							current = proved + unproved;
							currentProved = proved;
							//				Logger.err.print(".");
							changed();
						}
					}
					endProof();
					changed();
				} else {
					// should never happen (?)
					endProof();
					setError("Error starting proof", "No details available");
					changed();
				}
			} catch (RemoteException e) {
				setError(
					AbServer.getErrorReason(e),
					AbServer.getErrorDetails(e));
				endProof();
			}
		} finally {
			// "deletes" the jpov object so that it can be garbage collected.
			jpov = null;

			finished();
		}
	}

	/**
	 * Called if the proof is aborted by the user.
	 * <p>
	 * This method should perform the necessary cleanup (currently nothing).
	 */
	protected void proofAborted() {
		if (jpov != null)
			try {
				ab.abortProof();
			} catch (RemoteException e) {
				setError(
					AbServer.getErrorReason(e),
					AbServer.getErrorDetails(e));
			}
	}

	/**
	 * @see ProofTask#getProverName()
	 * 
	 * @return the name of the prover: "Atelier B".
	 */
	public String getProverName() {
		return "Atelier B";
	}

	/**
	 * Writes the pmi file associated with Atelier B.
	 * @param printer The file printer
	 * @param fi The current JML file
	 * @param output_directory The folder where the file is to be stored
	 * @throws IOException
	 **/
	private void printPmi(String name, JmlFile fi, File output_directory)
		throws IOException {

		PrintStream stream;
		OutputStream ostream = null;

		if (output_directory != null) {
			File f = new File(output_directory, name + ".pmi");
			ostream = new BufferedOutputStream(new FileOutputStream(f));
			stream = new PrintStream(ostream);
		} else {
			// if no output directory is given, print to stream
			stream = Logger.out;
		}
		// ensure that the file will be closed in case of error
		try {
			PmiPrinter pmiPrinter = new PmiPrinter(stream);
			pmiPrinter.printTheoryBalanceX(name, fi);
			pmiPrinter.printTheoryProofState(fi);
			pmiPrinter.printTheoryMethodList(fi);
			pmiPrinter.printTheoryPassList(fi);
		} finally {
			// close the file after printing (even if an exception is 
			// thrown)
			if (ostream != null) {
				try {
					ostream.close();
				} catch (IOException e) {
					Logger.err.println(
						"Error closing file: " + ostream.toString());
				}
			}
		}

	}

	/**
	 * Parses a pmi file
	 * @param ab The current Atelier B server
	 * @return the pmi as an AST tree
	 * @throws RemoteException
	 **/
	public AST importPmi(AbServer ab) throws RemoteException {
		File f = new File(jpov.getDirectory(), jpov.getName() + ".pmi");

		ab.readPmi(jpov.getName(), jpov.getDirectory());
		FileInputStream fs;
		PmiParser parser;
		try {
			fs = new FileInputStream(f);
		} catch (IOException e) {
			Logger.err.println("Exception catched : " + e.toString());
			return null;
		}
		try {
			PmiLexer lexer = new PmiLexer(fs);
			lexer.currentFile = f;
			parser = new PmiParser(lexer);
			parser.lexer = lexer;
			parser.currentFile = f;
			parser.errors = 0;
			parser.warnings = 0;
			parser.compilation_unit();
			parser.errors += lexer.errors;
		} catch (antlr.RecognitionException e) {
			Logger.err.println("Exception catched : " + e.toString());
			return null;
		} catch (antlr.TokenStreamException e) {
			Logger.err.println("Exception catched : " + e.toString());
			return null;
		} finally {
			try {
				fs.close();
			} catch (IOException e) {
				Logger.err.println("Error closing file: " + e.toString());
				return null;
			}
		}
		if (parser == null) {
			return null;
		}

		return parser.getAST();

	}

	/**
	 * Sets the status of the JML file lemma getting informations into a loaded
	 * pmi file
	 * @param pmiTree the {@link AST} corresponding to the pmi file
	 **/
	public void setStatus(AST pmiTree) {
		setStatus(extractStatus(pmiTree));
	}

	/**
	 * Extracts the status from a AST representing a pmi file
	 * @param pmiTree The AST tree corresponding to the pmi
	 * @return the array of extracted goals status
	 **/
	private ProverBStatus[] extractStatus(AST pmiTree) {
		int nbPo;
		ProverBStatus[] res =
			new ProverBStatus[nbPo = jpov.getJmlFile().getNbPo()];
		int current = nbPo;
		AST proofState =
			pmiTree.getFirstChild().getNextSibling().getFirstChild();
		while (proofState != null) {
			String text = proofState.getFirstChild().getText();
			if (text.equals("Unproved")) {
				res[--current] = new ProverBStatus();
			} else {
				text = proofState.getFirstChild().getNextSibling().getText();
				if (text.equals("Util")) {
					res[--current] =
						new ProverBStatus(ProverBStatus.PROVEDUTIL);
				} else {
					res[--current] =
						new ProverBStatus((byte) (text.charAt(0) - '0'));
				}
			}
			proofState = proofState.getNextSibling();
		}
		if (current != 0) {
			// should throw an exception.
		}
		AST methodList =
			pmiTree
				.getFirstChild()
				.getNextSibling()
				.getNextSibling()
				.getFirstChild();
		current = nbPo;
		while (methodList != null) {
			res[--current].setMethodList(
				parseProofScript(methodList.getFirstChild(), ""));
			methodList = methodList.getNextSibling();
		}
		return res;
	}

	/**
	 * Sets the status of lemmas depending of the read pmi file
	 * @param status The array of goal status extracted from a pmi file
	 **/
	private void setStatus(ProverBStatus[] status) {
		int current = 0;
		for (int i = 0; i < jpov.getJmlFile().getClasses().length; i++) {
			current =
				setStatus(jpov.getJmlFile().getClasses()[i], status, current);
		}
		jpov.getJmlFile().updateStatus();
	}

	/**
	 * Sets the status of lemmas depending of the read pmi file
	 * @param status The array of goal status extracted from a pmi file
	 * @param current The current index in the goal status array
	 * @return The updated index
	 **/
	public int setStatus(Class c, ProverBStatus[] status, int current) {
		current = setStatus(c.getStaticInitLemmas(), status, current);
		current = setStatus(c.getWellDefInvLemmas(), status, current);
		for (int i = 0; i < c.getConstructors().length; i++) {
			current =
				setStatus(c.getConstructors()[i].getLemmas(), status, current);
			current =
				setStatus(
					c.getConstructors()[i].getWellDefinednessLemmas(),
					status,
					current);
			c.getConstructors()[i].updateStatus();
		}
		for (int i = 0; i < c.getMethods().length; i++) {
			current = setStatus(c.getMethods()[i].getLemmas(), status, current);
			current =
				setStatus(
					c.getMethods()[i].getWellDefinednessLemmas(),
					status,
					current);
			c.getMethods()[i].updateStatus();
		}
		return current;
	}

	/**
	 * Sets the status of lemmas depending of the read pmi file
	 * @param status The array of goal status extracted from a pmi file
	 * @param current The current index in the goal status array
	 * @return The updated index
	 **/
	int setStatus(Proofs p, ProverBStatus[] status, int current) {
		for (int i = 0; i < p.getLemmas().length; i++)
			current = setStatus(p.getLemmas()[i], status, current);
		return current;
	}

	/**
	 * Sets the status of lemmas depending of the read pmi file
	 * @param status The array of goal status extracted from a pmi file
	 * @param current The current index in the goal status array
	 * @return The updated index
	 **/
	int setStatus(Lemma l, ProverBStatus[] status, int current) {
		for (int i = 0; i < l.getGoals().length; i++)
			l.getGoals()[i].setStatus("B", status[current++]);
		return current;
	}

	/* (non-Javadoc)
	 * @see jack.plugin.prove.ProofTask#proveGoals(java.lang.String, jpov.structure.Goal[], int)
	 */
	protected void proveGoals(String name, Goal[] goals, int cpt) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see jack.plugin.prove.ProofTask#factory()
	 */
	public ProveAction factory() {
		return new ProveBAction();
	}

}
