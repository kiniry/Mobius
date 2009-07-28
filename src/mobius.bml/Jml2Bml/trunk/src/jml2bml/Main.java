/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import jml2bml.ast.PrettyPrinter;
import jml2bml.ast.TreeNodeFinder;
import jml2bml.engine.Jml2BmlTranslator;
import jml2bml.engine.TranslationManager;
import jml2bml.exceptions.NotTranslatedException;
import jml2bml.exceptions.NotTranslatedRuntimeException;
import jml2bml.symbols.Symbols;
import jml2bml.utils.Logger;

import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.kohsuke.args4j.Argument;
import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;
import org.kohsuke.args4j.Option;

import annot.io.ReadAttributeException;

import com.sun.source.tree.LineMap;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;

/*
 * @author Jedrek
 */

public class Main {
  /**
   * Logger for this class.
   */
  private static final Logger log = Logger.getLogger(Main.class);

  @Option(name = "-o", usage = "output to this file", metaVar = "OUTPUT")
  private String out;

  @Option(name = "-v", usage = "verbose")
  private boolean verbose = false;

  @Argument
  private java.util.List < String > arguments = new ArrayList < String >();

  public void doMain(String[] args) throws IOException, CmdLineException,
      ClassNotFoundException, ReadAttributeException, NotTranslatedException {
    CmdLineParser parser = new CmdLineParser(this);
    parser.parseArgument(args);
    if (arguments.size() != 3)
      throw new CmdLineException("Invalid argument number");
    String inputDir = arguments.get(1);
    if (out == null)
      out = inputDir + "-wyn";
    compile(arguments.get(0), inputDir, out, "", null);
  }

  /**
   * Main method of the Jml2Bml compiler. For given class and source,
   * inserts into bytecode the translated Jml annotations from the source code.
   * @param args <code>args[0]</code> directory containing compiled classes<br>
   * <code>args[1]</code> class file name<br>
   * <code>args[2]</code> source file (whole path)
   * @throws ClassNotFoundException
   * @throws ReadAttributeException
   * @throws NotTranslatedException 
   * @throws CmdLineException 
   */
  public static void main(final String[] args) throws ClassNotFoundException,
      ReadAttributeException, IOException, CmdLineException,
      NotTranslatedException {
    new Main().doMain(args);
  }

  /**
   * Main method of the Jml2Bml compiler. Compiles JML annotations from
   * sourceFile and inserts appropriate BML annotations into classFile
   * @param sourceFile -
   *            source containing compiled JML
   * @param classLoc class file location (directory and filename)
   * corresponding to the source file
   * @throws ClassNotFoundException if the classfile for the
   *   given class file location could not be found
   * @throws ReadAttributeException if any of BML attributes was not correctly
   *   parsed by BMLlib library
   * @throws NotTranslatedException
   * @throws IOException in case the class file cannot be saved to the given
   *   location
   */
  public void compile(final String sourceFile,
                      final String binLocationDir,
                      final String outLocationDir,
                      final String classPath,
                      final PrintWriter printWriter)
      throws ClassNotFoundException, ReadAttributeException,
      NotTranslatedException, IOException {
    API api = new API(printWriter, new JmlDiagnosticListener(printWriter), "-cp", classPath);
    
//  final Context context = createContext(printWriter);
    
    final Context context = api.context();
//    context.put(ClassPath.class, new ClassPath(classPath));
    BCClassManager manager = new BCClassManager(binLocationDir, outLocationDir);
    context.put(BCClassManager.class, manager);
    

    List < JmlCompilationUnit > files = api.parseFiles(new File(sourceFile));
    final int errorsCount = api.enterAndCheck(files);
    final JmlCompilationUnit tree = files.get(0);
    
//    final JCCompilationUnit tree = files.head;
    //    final JCCompilationUnit tree = compiler
    //        .parse(getJavaFileObject(context, sourceFile));
    //
    ////    Build symbol table/type analysis
    //    ListBuffer < JCCompilationUnit > roots = lb();
    //    roots.append(tree);
    //    compiler.enterTrees(roots.toList());
    if (verbose) {
      log.info("------------- PRETTY PRINT ------------");
      new PrettyPrinter(System.out).prettyPrint(tree);
//      log.info("LINE TABLES: ");
//      for (Method m : clazz.getJC().getMethods()) {
//        log.info(m.getName());
//        final LineNumberTable lnt = m.getLineNumberTable();
//        if (lnt != null) {
//          log.info(lnt.toString());
//        } else {
//          log.info("NO LINE NUMBER TABLE!!!");
//        }
//      }
      log.info("----------- END PRETTY PRINT ----------");
    }
    context.put(LineMap.class, tree.getLineMap());

    context.put(JCCompilationUnit.class, tree);

    final TreeNodeFinder parentFinder = new TreeNodeFinder(tree);
    context.put(TreeNodeFinder.class, parentFinder);
    final Jml2BmlTranslator translator = TranslationManager
        .getTranslator(context);
    final Symbols syms = new Symbols();
    try {
      tree.accept(translator, syms);
    } catch (NotTranslatedRuntimeException e) {
      throw new NotTranslatedException(e);
    }
    
    manager.saveAll();
    System.out.println("Written to: " + out);

  }

//  /**
//   * Creates the application context and registers main components.
//   * @return created application context.
//   */
//  private Context createContext(PrintWriter printWriter) {
//    final Context context = new Context();
//    context.put(Log.outKey, printWriter);
//    JavacMessages.instance(context).add(Utils.messagesJML);// registering an additional source of JML-specific error messages
//
//    JmlSpecs.preRegister(context); // registering the specifications repository
//    JmlParser.JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlParsers
//    JmlScanner.JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlScanners
//    JmlTree.Maker.preRegister(context); // registering a JML-aware factory for generating JmlTree nodes
//    JmlCompiler.preRegister(context);
//    JmlEnter.preRegister(context);
//    JmlResolve.preRegister(context);
//    JmlMemberEnter.preRegister(context);
//    JmlFlow.preRegister(context);
//    JmlAttr.preRegister(context); // registering a JML-aware type checker
//    JmlPretty.preRegister(context);
//
//    //    
//    //    JmlSpecs.preRegister(context);
//    //    JmlParser.JmlFactory.preRegister(context);
//    //    JmlScanner.JmlFactory.preRegister(context);
//    //    JmlTree.Maker.preRegister(context);
//    //    JmlEnter.preRegister(context);
//    //    JmlResolve.preRegister(context);
//    //    JmlMemberEnter.preRegister(context);
//    //    JmlFlow.preRegister(context);
//    //    JmlAttr.preRegister(context);
//    JavacFileManager.preRegister(context);
//    final Options opts = Options.instance(context);
//    //
//    opts.put(OptionName.XJCOV.optionName, "true");
//
//    JmlSpecs.instance(context).initializeSpecsPath();
//    return context;
//  }

}
