/*
 * Created on Feb 23, 2005
 */
package coqPlugin.printers;

import java.io.File;
import java.io.PrintStream;

import jml2b.IJml2bConfiguration;

/**
 * @author jcharles
 */
public class UserExtensions extends Printer {
	String output_directory;
	
	public UserExtensions(File output_directory, IJml2bConfiguration config) {
		super(output_directory, "user_extensions.v");
		this.output_directory = output_directory.getAbsolutePath();
		startWriting(config);
		
	}
	
	
	protected void writeToFile(PrintStream stream, IJml2bConfiguration config){
		stream.println("Add LoadPath \"" + output_directory + "\".\n");
		stream.println("(* I am the fourth and final little helper. *)");
		stream.println("Require Import \"" + StaticPrelude1.fileName + "\".");
		stream.println("Require Import \"" + StaticPrelude2.fileName + "\".\n");
		stream.println("(** * The User Extensions Library *)\n");
		stream.println("Module UserExtensions (Arg: JackClasses).");

		stream.println("Module JackRefs := JackReferences Arg.");
		stream.println("Import JackRefs.");
		stream.println("Open Scope J_Scope.\n\n");
		
		stream.println("End UserExtensions.");
			
	} 
	
	

}
