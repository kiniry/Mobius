/*
 * Created on Feb 23, 2005
 *
 */
package coqPlugin.printers;

import jack.util.Logger;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import java.io.PrintStream;

import fr.inria.everest.coq.sugar.CoqUtils;

import prover.plugins.exceptions.ProverException;

import jml2b.IJml2bConfiguration;

/**
 * @author jcharles
 *
 */
public abstract class Printer {
	private File f;
	private String pathWithoutExtension;
	private String nameWithoutExtension;
	public Printer(File output_directory, String name) {
		f = new File(output_directory, name);
		String tmp = f.getAbsolutePath();
		pathWithoutExtension = f.getAbsolutePath();
		int i;
		if((i = tmp.lastIndexOf('.')) != -1) {
			pathWithoutExtension = tmp.substring(0, i);
		}
		tmp = f.getName();
		nameWithoutExtension = f.getName();
		if((i = tmp.lastIndexOf('.')) != -1) {
			nameWithoutExtension = tmp.substring(0, i);
		}
	}
	public boolean mustRewrite() {
		return false;
	}
	
	public void startWriting(IJml2bConfiguration config) {
		if(mustRewrite() || !f.exists()) {
			PrintStream stream;
			try {
				stream = new PrintStream(new BufferedOutputStream(new FileOutputStream(f)));
				writeToFile(stream, config);
				stream.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	protected abstract void writeToFile(PrintStream stream, IJml2bConfiguration config);
	/**
	 * @return
	 */
	public String getAbsolutePath() {
		return f.getAbsolutePath();
	}
	public String getAbsolutePathWithoutExtension() {
		return this.pathWithoutExtension;
	}
	public String getNameWithoutExtension() {
		return this.nameWithoutExtension;
	}
	public String toString() {
		String name = f.getAbsolutePath();
		return name.substring(0, name.lastIndexOf('.'));
	}
	public void compile() throws ProverException {
		//String [] path = {f.getParentFile().getAbsolutePath()};
		String [] cmdCoqC = (CoqUtils.getCommand(null, f.getAbsolutePath()));
		Process p;
		boolean bWasCompiled = true;

		String res = "";
		try {
			p = Runtime.getRuntime().exec(cmdCoqC);
			LineNumberReader in = new LineNumberReader( new InputStreamReader(p.getInputStream()));
			String s;
			while((s = in.readLine()) != null){
				res += s;
				Logger.get().println(res);
				if (s.matches("Error.*")) 
					bWasCompiled = false;
			}
			in = new LineNumberReader( new InputStreamReader(p.getErrorStream()));
			while((s = in.readLine()) != null){
				res += s;

				Logger.get().println(res);
				if (s.matches("Error.*")) 
					bWasCompiled = false;
			}
		} catch (IOException e) {
			Logger.err.println("I was unable to find the path to coqc. Check the path.");
			e.printStackTrace();
		}
		if (!bWasCompiled) {
			throw new ProverException("There was an error in " + getAbsolutePath() + ".\n" + res);
		}
	}
	private String moduleName;
	public String getModule() {
		return  moduleName;
	}
	protected void setModule(String module) {
		moduleName = module;
	}
}
