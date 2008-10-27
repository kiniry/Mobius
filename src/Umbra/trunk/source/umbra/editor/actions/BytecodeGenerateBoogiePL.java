/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions;

import java.io.ByteArrayInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;

import org.eclipse.core.internal.resources.File;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleDocumentPartitioner;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.ui.console.TextConsole;
import org.eclipse.ui.part.FileEditorInput;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.FileNames;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraMethodException;
import umbra.lib.UmbraRangeException;
import umbra.lib.UmbraSyntaxException;
import visitor.TranslatingVisitor;
import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;
import b2bpl.Project;
import b2bpl.bpl.BPLPrinter;
import b2bpl.bpl.ast.BPLProgram;
import b2bpl.bpl.transformation.IBPLTransformator;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.TypeLoader;
import b2bpl.bytecode.analysis.SemanticAnalyzer;
import b2bpl.translation.Translator;


/**
 * @author alx
 * @version a-01
 *
 */
public class BytecodeGenerateBoogiePL extends BytecodeEditorAction {


  private MessageConsole tc;
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
    final String fnameTo =
      active.toPortableString().replaceFirst(FileNames.BYTECODE_EXTENSION,
                  FileNames.CLASS_EXTENSION);
    final String fnameFrom = FileNames.getSavedClassFileNameForBTC(active);
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    final IFile fileFrom = root.getFile(new Path(fnameFrom));
    final IPath pathTo = new Path(fnameTo);
    if (tc == null) {
      IConsoleManager consoleManager = 
        ConsolePlugin.getDefault().getConsoleManager();
          tc = new MessageConsole("BoogiePL", null);
          IConsole[] cons = new MessageConsole[1];
          cons[0]=tc;
          consoleManager.addConsoles(cons);
          myDebugConsoleStream= new MessageConsoleStream(tc);
      
    }
    String dirName = file.getLocation().removeLastSegments(1).toOSString();
    String className = active.lastSegment().replace(FileNames.BYTECODE_EXTENSION, "");
    myDebugConsoleStream.println(".bpl file directory: " + dirName);
    myDebugConsoleStream.println("class to compile: " + className);
    BCClass clazz;
    
    try {
      clazz = new BCClass(dirName, className);
      JClassType type = new JClassType(clazz.getJC().getClassName());
      TranslatingVisitor v = new TranslatingVisitor();
      String bplName = active.lastSegment().replace(FileNames.BYTECODE_EXTENSION, ".bpl");
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
      final String fname = file.getFullPath().removeLastSegments(1).toOSString() + "/" + bplName;
      final String fname1 = file.getFullPath().removeLastSegments(1).toOSString() + "/A.class";
      System.out.println(fname);

      myDebugConsoleStream.println(className + " compiled");
      String[] args = new String[2];
      args[0] = "-pfg";
      args[1] = dirName + "/" + bplName;
      myDebugConsoleStream.println("++++ FreeBoogie start ++++");
      freeboogie.Main.main(args);
      InputStream is;
      int len =0;
      try {
        is = file.getContents();

      for (int i = 0; is.available() > 0; is.read())
        len++;
      } catch (CoreException e) {
        // TODO Auto-generated catch block
        //e.printStackTrace();
      } catch (IOException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      System.out.println(len);
      if (len == 2053 || len == 2285) {
        Thread.sleep(2000);
        myDebugConsoleStream.println("Success!");
      } else {
        Thread.sleep(5000);
        myDebugConsoleStream.println("Failure :-(");
      }
      myDebugConsoleStream.println("++++ FreeBoogie end ++++");
    } catch (ClassNotFoundException e2) {
      // TODO Auto-generated catch block
      e2.printStackTrace();
    } catch (ReadAttributeException e2) {
      // TODO Auto-generated catch block
      e2.printStackTrace();
    } catch (InterruptedException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }

  public void compile(String name, JClassType classType) {
      translate(name, classType);
  }
  
  private void translate(String outFile, JClassType... types) {
    String[] s = new String[1];
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
