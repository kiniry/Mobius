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
 * @author alx
 * @version a-01
 */
public class BytecodeGenerateBoogiePL extends BytecodeEditorAction {

  /**
   * The console which will contain the BoogiePL output.
   */
  private MessageConsole tc;

  /**
   * 
   */
  private MessageConsoleStream myDebugConsoleStream;

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
   * This method restores a saved copy of the original .class file that resulted
   * from the Java source file (it is stored under the name of the class file
   * prefixed with '_'). The class file with our modifications is removed, and
   * the editor input is updated together with the editor window.
   *
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
    myDebugConsoleStream.println(".bpl file directory: " + dirName);
    myDebugConsoleStream.println("class to compile: " + className);
    try {
      final String bplName = compileToBPL(active, dirName, className);
      checkBPL(dirName, bplName);
    } catch (ClassNotFoundException e2) {
      // TODO Auto-generated catch block
      e2.printStackTrace();
    } catch (ReadAttributeException e2) {
      // TODO Auto-generated catch block
      e2.printStackTrace();
    }
  }

  /**
   * @param dirName
   * @param bplName
   */
  private void checkBPL(String dirName, String bplName) {
    String[] args = new String[2];
    args[0] = "-pfg";
    args[1] = dirName + "/" + bplName;
    myDebugConsoleStream.println("++++ FreeBoogie start ++++");
    freeboogie.Main.main(args);
  }

  /**
   * @param active
   * @param dirName
   * @param className
   * @return
   * @throws ClassNotFoundException
   * @throws ReadAttributeException
   */
  private String compileToBPL(final IPath active, String dirName,
                              String className) throws ClassNotFoundException,
      ReadAttributeException {
    BCClass clazz;
    clazz = new BCClass(dirName, className);
    final JClassType type = new JClassType(clazz.getJC().getClassName());
    final TranslatingVisitor v = new TranslatingVisitor();
    String bplName = active.lastSegment().replace(
      FileNames.BYTECODE_EXTENSION, ".bpl");
    try {
      compile(bplName, v.visit(clazz));
      System.out.println(type.getDescriptor());
    } catch (NullPointerException e) {
      //e.printStackTrace();
      try {
        compile(bplName, v.visit(clazz));
      } catch (NullPointerException e1) {
      }
    }
    myDebugConsoleStream.println(className + " compiled");
    return bplName;
  }

  /**
   * This method lazily returns the console into which the BoogiePL verification
   * output will be printed out.
   *
   * @return the console
   */
  public MessageConsole getDebugConsole() {
    if (tc == null) {
      final IConsoleManager consoleManager =
        ConsolePlugin.getDefault().getConsoleManager();
      tc = new MessageConsole("BoogiePL", null);
      final IConsole[] cons = new MessageConsole[1];
      cons[0] = tc;
      consoleManager.addConsoles(cons);
      myDebugConsoleStream = new MessageConsoleStream(tc);
    }
    return tc;
  }

  public void compile(String outFile, JClassType... types) {
    final String[] s = new String[1];
    s[0] = outFile.replace(".bpl", ".class");
    Project project = Project.fromCommandLine(s,
                       new PrintWriter(System.out));
    b2bpl.Main main = new b2bpl.Main(project);
    TypeLoader.setProject(project);
    TypeLoader.setProjectTypes(project.getProjectTypes());
    TypeLoader.setSpecificationProvider(project.getSpecificationProvider());
    TypeLoader.setSemanticAnalyzer(new b2bpl.bytecode.analysis.SemanticAnalyzer(project, main));
    TypeLoader.setTroubleReporter(main);
    BPLProgram program = new Translator(project).translate(types);

    for (IBPLTransformator transformator : project.getTransformators()) {
      program = transformator.transform(program);
    }

    try {
      PrintWriter writer;
      if ("-".equals(outFile)) {
        writer = new PrintWriter(System.out);
      } else {
        writer = new PrintWriter(new FileOutputStream(outFile));
      }
      program.accept(new BPLPrinter(writer));
      writer.flush();
      writer.close();

    } catch (FileNotFoundException e) {
      e.printStackTrace();
    }
  }
}
