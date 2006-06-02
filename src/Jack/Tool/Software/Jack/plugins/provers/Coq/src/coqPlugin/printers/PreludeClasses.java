package coqPlugin.printers;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import jml2b.IJml2bConfiguration;
import jml2b.pog.printers.AClassEnumeration;
import jml2b.pog.printers.IClassResolver;
import jml2b.pog.printers.IPrinter;
import jml2b.structure.java.AClass;

public class PreludeClasses extends Printer{
	private IClassResolver printer;

	private String[] builtinNames = IPrinter.builtinNames;
	private String outDir;

	private boolean fHasObject;
	
	public PreludeClasses(File output_directory, String name, IClassResolver printer, IJml2bConfiguration config)
		throws IOException {
		super(output_directory, name +  "_classes.v");
		this.printer = printer;
			
		outDir = output_directory.getAbsolutePath() + File.separator;
		this.setModule(name + "Classes");
		startWriting(config);
		
	}
	
	
	public boolean mustRewrite() {
		return true;
	}

	protected void writeToFile(PrintStream stream, IJml2bConfiguration config) {
		stream.println("Add LoadPath \"" + outDir + "\".");
		stream.println("Require Import \"" +StaticPrelude2.fileName + "\".");
		
		stream.println("Module " + getModule() + " <: JackClasses.");
		defineClasses(stream);
		stream.println("Definition Classes := Class.");
		stream.println("Definition IntClass := c_int.");
		stream.println("Definition ShortClass := c_short.");
		stream.println("Definition ByteClass := c_byte.");
		stream.println("Definition CharClass := c_char.");
		stream.println("Definition BooleanClass := c_boolean.");
//		IClass cl = config.getPackage().getJavaLangString();
//		if(cl != null) {
//			stream.println("Definition StringClass := " + cl.getBName() + ".");
//		}
//		else
		stream.println("Definition StringClass := c_Object.");
		
		stream.println("End " + getModule() + ".\n");
	}
	
	/**
	 * Prints the inductive definition of the set representing the classes
	 * @param stream
	 **/
	private void defineClasses(PrintStream stream) {
		stream.println("");
		stream.println("(* Class Definitions *)");
		stream.println("Inductive Class : Set");
		stream.print("   := ");
		fHasObject = false;
		
		// print builtin types
		for (int i = 0; i < builtinNames.length; ++i) {
			if (i != 0)
				stream.print("\n      | ");
			if(builtinNames[i].equals("c_Object"))
				fHasObject = true;
			stream.print(builtinNames[i] + " : Class");
		}

		// print classes
		defineClasses(stream, printer.getClasses());
		defineClasses(stream, printer.getInterfaces());
		if(!fHasObject) {
			stream.print("\n      | ");
			stream.print("c_Object : Class");
		}
		stream.println(".\n");
	}

	/**
	 * Prints the classes as member of the inductive classes set
	 * @param e The set of classes
	 **/
	private void defineClasses(PrintStream stream, AClassEnumeration e) {
		while (e.hasMoreElements()) {
			AClass c = e.nextElement();
			if(!c.getModifiers().isNative()) {
				stream.print("\n      | ");
				if(c.getBName().equals("c_Object"))
					fHasObject = true;
				stream.print(c.getBName() + " : Class");
			}
		}
	}
}
