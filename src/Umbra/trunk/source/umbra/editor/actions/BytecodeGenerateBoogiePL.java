/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.ui.part.FileEditorInput;

import freeboogie.Main;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditorContributor;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.FileNames;
import visitor.TranslatingVisitor;
import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;
import b2bpl.Project;
import b2bpl.bpl.BPLPrinter;
import b2bpl.bpl.ast.BPLProgram;
import b2bpl.bpl.transformation.IBPLTransformator;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.TypeLoader;
import b2bpl.translation.Translator;


/**
 * This class defines action of compilation of the bytecode file to BoogiePL
 * and checking the BoogiePL file with FreeBogie.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeGenerateBoogiePL extends BytecodeEditorAction {

  /**
   * The number of command line arguments supplied to FreeBoogie.
   */
  private static final int NO_OF_FREEBOOGIE_ARGS = 2;

  /**
   * The console which will contain the BoogiePL output.
   */
  private MessageConsole my_message_console;

  /**
   * The stream associated with the current console.
   */
  private MessageConsoleStream my_console_stream;

  /**
   * This constructor creates the action to restore the original contents
   * of the class file. It registers the name of the action and stores
   * locally the object which creates all the actions
   * and which contributes the editor GUI elements to the eclipse GUI.
   *
   * @param a_contributor the manager that initialises all the actions within
   *   the byte code plugin
   * @param a_bytecode_contribution the GUI elements contributed to the eclipse
   *   GUI by the byte code editor. This reference should be the same as in the
   *   parameter <code>a_contributor</code>.
   */
  public BytecodeGenerateBoogiePL(final BytecodeEditorContributor a_contributor,
                         final BytecodeContribution a_bytecode_contribution) {
    super(EclipseIdentifiers.GENBPL_ACTION_NAME, a_contributor,
          a_bytecode_contribution);
  }

  /**
   * This method compiles the class file to BoogiePL and then runs FreeBoogie
   * to verify the correctness of the bytecode with regard to the BML
   * specifications.
   */
  public final void run() {
    final Shell parent = getEditor().getSite().getShell();
    final IFile file = ((FileEditorInput)getEditor().getEditorInput()).
                                                     getFile();
    final IPath active = file.getFullPath();
    getDebugConsole();
    final String dirName = file.getLocation().removeLastSegments(1).
      toOSString();
    final String className = active.lastSegment().replace(
      FileNames.BYTECODE_EXTENSION, "");
    my_console_stream.println(".bpl file directory: " + dirName);
    my_console_stream.println("class to compile: " + className);
    try {
      final String bplName = compileToBPL(active, dirName, className);
      checkBPL(dirName, bplName);
    } catch (ClassNotFoundException e2) {
      wrongPathToClassMessage(parent, getDescription(), dirName + "/" +
                              className);
    } catch (ReadAttributeException e2) {
      wrongBMLAttribute(parent, getDescription());
    }
  }

  /**
   * This method verifies the BoogiePL file using FreeBoogie. It checks the
   * file under the location being the concatenation of <code>a_dirname</code>
   * and <code>a_bplname</code>.
   *
   * @param a_dirname a directory with the BoogiePL file
   * @param a_bplname a BoogiePL file name
   */
  private void checkBPL(final String a_dirname,
                        final String a_bplname) {
    final String[] args = new String[NO_OF_FREEBOOGIE_ARGS];
    args[0] = "-pfg";
    args[1] = a_dirname + "/" + a_bplname;
    my_console_stream.println("++++ FreeBoogie start ++++");
    Main.main(args);
  }

  /**
   * Compiles the file specifed by <code>a_dirname</code> and
   * <code>a_classname</code> from the bytecode format to BoogiePL format.
   *
   * @param an_active the path to the current bytecode file
   * @param a_dirname path of directory where .class file to compile to BoogiePL
   *   is located, excluding directories included in <code>a_classname</code>
   * @param a_classname the name of the file with the class to be translated
   * @return the name of the BoogiePL file
   * @throws ClassNotFoundException if .class file designated by
   *   <code>a_classname</code> could not be found
   * @throws ReadAttributeException if any of the BML attributes was not
   *   correctly parsed by BMLlib
   */
  private String compileToBPL(final IPath an_active,
                              final String a_dirname,
                              final String a_classname)
    throws ClassNotFoundException, ReadAttributeException {
    BCClass clazz;
    clazz = new BCClass(a_dirname, a_classname);
    final TranslatingVisitor v = new TranslatingVisitor();
    final String bplName = an_active.lastSegment().replace(
      FileNames.BYTECODE_EXTENSION, FileNames.BOOGIEPL_EXTENSION);
    try {
      compile(bplName, v.visit(clazz));
    } catch (NullPointerException e) {
      e.printStackTrace(); // TODO strange ????
      try {
        compile(bplName, v.visit(clazz));
      } catch (NullPointerException e1) {
        e1.printStackTrace(); // TODO strange ????
      }
    }
    my_console_stream.println(a_classname + " compiled to BoogiePL");
    return bplName;
  }

  /**
   * This method lazily returns the console into which the BoogiePL verification
   * output will be printed out.
   *
   * @return the console
   */
  public MessageConsole getDebugConsole() {
    if (my_message_console == null) {
      final IConsoleManager consoleManager =
        ConsolePlugin.getDefault().getConsoleManager();
      my_message_console = new MessageConsole("BoogiePL", null);
      final IConsole[] cons = new MessageConsole[1];
      cons[0] = my_message_console;
      consoleManager.addConsoles(cons);
      my_console_stream = new MessageConsoleStream(my_message_console);
    }
    return my_message_console;
  }

  /**
   * The method compiles the BoogiePL output out of the current bytecode.
   *
   * @param an_outfile the name of the output to be generated
   * @param the_types the types of the classes to be compiled
   */
  public void compile(final String an_outfile,
                      final JClassType the_types) {
    final String[] s = new String[1];
    s[0] = an_outfile.replace(FileNames.BOOGIEPL_EXTENSION,
                              FileNames.CLASS_EXTENSION);
    final Project project = Project.fromCommandLine(s,
                       new PrintWriter(System.out));
    final b2bpl.Main main = new b2bpl.Main(project);
    TypeLoader.setProject(project);
    TypeLoader.setProjectTypes(project.getProjectTypes());
    TypeLoader.setSpecificationProvider(project.getSpecificationProvider());
    TypeLoader.setSemanticAnalyzer(
      new b2bpl.bytecode.analysis.SemanticAnalyzer(project, main));
    TypeLoader.setTroubleReporter(main);
    BPLProgram program = new Translator(project).translate(the_types);

    final IBPLTransformator[] transformators = project.getTransformators();
    for (int i = 0; i < transformators.length; i++) {
      program = transformators[i].transform(program);
    }
    generateBPLFile(program, an_outfile);
  }

  /**
   * This method generates the file with BoogiePL output.
   *
   * @param a_prog the program to generate BoogiePL output from
   * @param an_outfile the name of the file to generate output to
   */
  private void generateBPLFile(final BPLProgram a_prog,
                               final String an_outfile) {
    try {
      PrintWriter writer;
      if ("-".equals(an_outfile)) {
        writer = new PrintWriter(System.out);
      } else {
        writer = new PrintWriter(new FileOutputStream(an_outfile));
      }
      a_prog.accept(new BPLPrinter(writer));
      writer.flush();
      writer.close();

    } catch (FileNotFoundException e) {
      e.printStackTrace();
    }
  }
}
