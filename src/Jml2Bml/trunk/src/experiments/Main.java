/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-06 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package experiments;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import jml2bml.ast.PrettyPrinter;
import jml2bml.ast.TreeNodeFinder;
import jml2bml.bytecode.ClassFileLocation;
import jml2bml.engine.Jml2BmlTranslator;
import jml2bml.engine.Symbols;
import jml2bml.engine.TranslationManager;

import org.jmlspecs.openjml.JmlTree;

import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;

import com.sun.source.tree.LineMap;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacFileManager;
import com.sun.tools.javac.util.List;

/**
 * @author Jedrek
 */

public class Main {
  public static void main(String[] args) throws ClassNotFoundException,
      ReadAttributeException {
    ClassFileLocation classLoc = new ClassFileLocation(
                                                       ProjectDirectory.PROJECT_DIR
                                                           + "\\bin",
                                                       "experiments.Test");
    new Main().compile(ProjectDirectory.PROJECT_DIR
                       + "\\src\\experiments\\Test.java", classLoc);
  }

  /**
   * Main method of the Jml2Bml compiler. Compiles JML annotations from
   * sourceFile and inserts appropriate BML annotations into classFile
   * 
   * @param sourceFile -
   *            source containing compiled JML
   * @param classFile -
   *            class file corresponding to the source file
   * @throws ReadAttributeException 
   * @throws ClassNotFoundException 
   */
  public void compile(String sourceFile, ClassFileLocation classLoc)
      throws ClassNotFoundException, ReadAttributeException {
    Context context = Factory.getContext();
    context.put(ClassFileLocation.class, classLoc);
    BCClass clazz = new BCClass(classLoc.getDirectoryName(), 
                                classLoc.getClassQualifiedName());
    context.put(BCClass.class, clazz);
    JavaCompiler compiler = JavaCompiler.instance(context);
    JCCompilationUnit tree = compiler.parse(getJavaFileObject(context,
                                                              sourceFile));

    new PrettyPrinter(System.out).prettyPrint(tree);
    context.put(LineMap.class, tree.getLineMap());
    
    TreeNodeFinder parentFinder = new TreeNodeFinder(tree);
    // TODO: move from context
    context.put(TreeNodeFinder.class, parentFinder);
    Jml2BmlTranslator translator = TranslationManager.getTranslator(context);
    Symbols syms = new Symbols();
    syms.setClass(context.get(BCClass.class));
    tree.accept(translator, syms);
    JmlEnter enter = (JmlEnter) JmlEnter.instance(context);
    ((JmlTree.JmlCompilationUnit) tree).mode = JmlTree.JmlCompilationUnit.JAVA_SOURCE_FULL;
    enter.visitTopLevel(tree);

    System.out.println("envir " + enter.getTopLevelEnv(tree));
    
    clazz.saveJC();
    System.out.println(clazz.printCode());
    System.out.println(clazz.printCp());
  }

  private JavaFileObject getJavaFileObject(Context context, String filename) {
    JavacFileManager fm = (JavacFileManager) context.get(JavaFileManager.class);
    return fm.getJavaFileObjectsFromStrings(List.of(filename)).iterator()
        .next();
  }
}
