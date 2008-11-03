/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package main;

import java.io.IOException;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import jml2bml.ast.PrettyPrinter;
import jml2bml.ast.TreeNodeFinder;
import jml2bml.bytecode.ClassFileLocation;
import jml2bml.engine.Jml2BmlTranslator;
import jml2bml.engine.TranslationManager;
import jml2bml.exceptions.NotTranslatedException;
import jml2bml.exceptions.NotTranslatedRuntimeException;
import jml2bml.symbols.Symbols;
import jml2bml.utils.Logger;

import org.apache.bcel.classfile.LineNumberTable;
import org.apache.bcel.classfile.Method;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;

import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;

import com.sun.source.tree.LineMap;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlFlow;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.OptionName;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacFileManager;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Options;

/**
 * @author Jedrek
 */

public class Main {
  /**
   * Logger for this class.
   */
  private static final Logger log = Logger.getLogger(Main.class);

  /**
   * Main method of the Jml2Bml compiler. For given class and source,
   * inserts into bytecode the translated Jml annotations from the source code.
   * @param args <code>args[0]</code> directory containing compiled classes<br>
   * <code>args[1]</code> class file name<br>
   * <code>args[2]</code> source file (whole path)
   * @throws ClassNotFoundException
   * @throws ReadAttributeException
   */
  public static void main(final String[] args) throws ClassNotFoundException,
      ReadAttributeException, IOException {
    if (args.length != 3) {
      return;
    }
    final main.List list = new main.List();
    try {
      new Main().compile(args[2], new ClassFileLocation(args[0], args[1]));
    } catch (NotTranslatedException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }

  /**
   * Main method of the Jml2Bml compiler. Compiles JML annotations from
   * sourceFile and inserts appropriate BML annotations into classFile
   * @param sourceFile -
   *            source containing compiled JML
   * @param classLoc class file location (directory and filename)
   * corresponding to the source file
   * @throws ReadAttributeException
   * @throws ClassNotFoundException
   * @throws NotTranslatedException
   * @throws IOException in case the class file cannot be saved to the given
   *   location
   */
  public void compile(final String sourceFile, final ClassFileLocation classLoc)
      throws ClassNotFoundException, ReadAttributeException,
      NotTranslatedException, IOException {
    final Context context = createContext();
    context.put(ClassFileLocation.class, classLoc);
    final BCClass clazz = new BCClass(classLoc.getDirectoryName(), classLoc
        .getClassQualifiedName());
    context.put(BCClass.class, clazz);
    final JavaCompiler compiler = JavaCompiler.instance(context);
    final JCCompilationUnit tree = compiler
        .parse(getJavaFileObject(context, sourceFile));

    log.info("------------- PRETTY PRINT ------------");
    new PrettyPrinter(System.out).prettyPrint(tree);
    log.info("LINE TABLES: ");
    for (Method m : clazz.getJC().getMethods()) {
      log.info(m.getName());
      final LineNumberTable lnt = m.getLineNumberTable();
      if (lnt != null) {
        log.info(lnt.toString());
      } else {
        log.info("NO LINE NUMBER TABLE!!!");
      }
    }
    log.info("----------- END PRETTY PRINT ----------");
    context.put(LineMap.class, tree.getLineMap());

    context.put(JCCompilationUnit.class, tree);

    final TreeNodeFinder parentFinder = new TreeNodeFinder(tree);
    context.put(TreeNodeFinder.class, parentFinder);
    final Jml2BmlTranslator translator = TranslationManager
        .getTranslator(context);
    final Symbols syms = new Symbols();
    syms.setClass(context.get(BCClass.class));
    try {
      tree.accept(translator, syms);
    } catch (NotTranslatedRuntimeException e) {
      throw new NotTranslatedException(e);
    }

    clazz.saveToFile(classLoc.getClassFilePath());
    log.info(clazz.printCode());
  }

  /**
   * Creates a Java File Object for given source file.
   * @param context application context
   * @param filename source file name
   * @return corresponding java file
   */
  private JavaFileObject getJavaFileObject(final Context context,
                                           final String filename) {
    final JavacFileManager fm = (JavacFileManager) context
        .get(JavaFileManager.class);
    return fm.getJavaFileObjectsFromStrings(List.of(filename)).iterator()
        .next();
  }

  /**
   * Creates the application context and registers main components.
   * @return created application context.
   */
  private Context createContext() {
    final Context context = new Context();
    JmlSpecs.preRegister(context);
    JmlParser.JmlFactory.preRegister(context);
    JmlScanner.JmlFactory.preRegister(context);
    JmlTree.Maker.preRegister(context);
    JmlEnter.preRegister(context);
    JmlResolve.preRegister(context);
    JmlMemberEnter.preRegister(context);
    JmlFlow.preRegister(context);
    JmlAttr.preRegister(context);
    JavacFileManager.preRegister(context);
    final Options opts = Options.instance(context);

    opts.put(OptionName.XJCOV.optionName, "true");

    return context;
  }

}
