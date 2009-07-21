package input;

import java.io.File;
import java.util.List;
import java.util.Vector;
import java.util.logging.Logger;

import javax.lang.model.element.ElementKind;

import log.CCLevel;
import log.CCLogRecord;
import main.Beetlz;

import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;

import static com.sun.tools.javac.code.Flags.*;

import structure.ClassCollection;
import structure.ClassStructure;
import structure.FeatureStructure;
import utils.BConst;

/**
 * Collects all Java input files and the parsed class structures,
 * if available.
 * Hence, the class is responsible for storing and initialisation and
 * control of parsing with the help of OpenJMl.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class JmlFile {
  /** Input files.  */
  private final List < File > my_files;

  /** Parsed classes.  */
  private final ClassCollection my_classCollection;
  /** Fully qualified names of all classes. */
  private final List < String > my_qualifiedNames;

  /** Our Logger for this session.  */
  private static final Logger LOGGER = Logger.getLogger(BConst.LOGGER_NAME);



  /**
   * Creates a new empty container for Jml files.
   */
  public JmlFile() {
    my_classCollection = new ClassCollection();
    my_files = new Vector < File > ();
    my_qualifiedNames = new Vector < String > ();
  }

  /**
   * Add a new file by path but don't process.
   * @param some_file_names list of input file names
   */
  public final void addFiles(final List < String > some_file_names) {
    for (final String s : some_file_names) {
      final File temp = new File(s);
      if (!my_files.contains(temp)) { //ignore duplicate files
        if (temp.exists()) {
          LOGGER.config(Beetlz.getResourceBundle().getString("JmlFile.fileFound") +
                        temp.getAbsolutePath()); //$NON-NLS-1$
          my_files.add(temp);
        } else {
          LOGGER.severe(Beetlz.
                        getResourceBundle().getString("JmlFile.cannotFindFile") + //$NON-NLS-1$
                        s);
        }
      }
    }
  }

  /**
   * Parse all files.
   * @return true if successful
   */
  public final boolean parseAll() {
    if (my_files.size() == 0) {
      return true;
    }
    try {
      Main m;
      if (Beetlz.getProfile().getSpecs() != null && Beetlz.getProfile().verbose()) {
        m = new Main(new String[]{"-specs", Beetlz.getProfile().getSpecs(), //$NON-NLS-1$
                                  "-noInternalSpecs", //$NON-NLS-1$
                                  "-verbose"}); //$NON-NLS-1$
      } else if (Beetlz.getProfile().getSpecs() != null) {
        m = new Main(new String[]{"-specs", Beetlz.getProfile().getSpecs(), //$NON-NLS-1$
                                  "-noInternalSpecs"}); //$NON-NLS-1$
      } else {
        m = new Main(new String[0]);
      }
      final File[] fileArray = my_files.toArray(new File[my_files.size()]);
      try {
        m.parseAndCheck(fileArray);
      } catch (final NullPointerException e) {
        Beetlz.getWaitingRecords().
          add(new CCLogRecord(CCLevel.COMPILATION_ERROR, null,
                            String.format(Beetlz.getResourceBundle().
                                          getString("JmlFile.compilError")))); //$NON-NLS-1$
        return false;
      }

      for (final File f : my_files) {
        final JmlCompilationUnit cu = m.parseFile(f.getAbsoluteFile());

        if (cu == null) {
          LOGGER.severe(String.format(Beetlz.getResourceBundle().
                                      getString("JmlFile.skippingNoUnit"), //$NON-NLS-1$
                                      f.getName()));
          continue;
        }
        final JmlWalker walker = new JmlWalker(cu);
        cu.accept(walker);
        my_qualifiedNames.addAll(walker.getQualifiedNames());

        for (final String qName : walker.getQualifiedNames()) {
          if (!Beetlz.getProfile().isJavaIgnored(qName)) {
            final ClassSymbol sym = m.getClassSymbol(qName);
            if (sym != null) {
              final JCTree ast = m.getClassAST(qName);
              parseClass(ast, sym, m, cu, null); //no enclosing class, top level
            } else {
              LOGGER.severe(String.format(Beetlz.getResourceBundle().
                                          getString("JmlFile.noClassSymbol"), //$NON-NLS-1$
                                          f.getName()));
            }
          }
        } //end for
      }
    } catch (final Exception e) {
      LOGGER.severe(Beetlz.getResourceBundle().
                    getString("JmlFile.cannotParseJml")); //$NON-NLS-1$
      e.printStackTrace(Beetlz.getErrorStream());
      return false;
    }

    return true;
  }

  /**
   * Parse a class.
   * @param an_ast AST to parse
   * @param a_symbol symbol to parse
   * @param a_main OpenJml main method
   * @param a_cu compilation unit
   * @param an_enclosing enclosing class
   * @return class structure
   */
  private ClassStructure parseClass(final JCTree an_ast, final ClassSymbol a_symbol,
                                    final Main a_main, final JmlCompilationUnit a_cu,
                                    final ClassStructure an_enclosing) {
    if (a_symbol.getKind() != ElementKind.ANNOTATION_TYPE) {
      if (an_ast instanceof JCClassDecl) {
        try {
          //parse the class
          final TypeSpecs cs = a_main.getSpecs(a_symbol);
          final ClassStructure cls = JmlParser.parseClass((JCClassDecl)an_ast, cs, a_symbol,
                                                          a_symbol.flatname.toString(),
                                                          an_enclosing, a_cu);
          if (a_symbol != null && a_symbol.members() != null &&
              a_symbol.members().getElements() != null) {
            for (final Symbol member : a_symbol.members().getElements()) {
              //parse methods
              if (member instanceof MethodSymbol) {
                if (member.isConstructor() && (member.flags_field & GENERATEDCONSTR) != 0) {
                  continue;
                }

                final JmlMethodSpecs ms = a_main.getSpecs((MethodSymbol)member);
                if (ms != null) {
                  final FeatureStructure feat = JmlParser.parseMethod(ms.decl, ms, cls, a_cu);
                  if (Beetlz.getProfile().noJml() && feat.isModel()) {
                    continue;
                  }
                  if (member.isConstructor()) { //add constructor elsewhere
                    cls.addConstructor(feat);
                  } else { //add everything else
                    cls.addFeature(feat);
                  }
                }
              //end method
              } else if (member instanceof VarSymbol) {
                final FieldSpecs fs = a_main.getSpecs((VarSymbol)member);
                if (fs != null) {
                  final FeatureStructure feat =
                    JmlParser.parseVariable((VarSymbol)member, fs, cls, a_cu);
                  if (Beetlz.getProfile().noJml() && (feat.isModel() || feat.isGhost())) {
                    continue;
                  }
                  cls.addFeature(feat);
                }
              //end variable
              } else if (member instanceof ClassSymbol) {
                if (!Beetlz.getProfile().
                    isJavaIgnored(((ClassSymbol) member).flatname.toString())) {
                  final JCTree ast =
                    a_main.getClassAST(((ClassSymbol) member).flatname.toString());
                  final ClassStructure memberClass =
                    parseClass(ast, (ClassSymbol)member, a_main, a_cu, cls);
                  cls.addAggregation(memberClass.getName());
                }
              } //end member class

            }
          }
          my_classCollection.addClass(cls);
          return cls;
        } catch (final Exception e) {
          LOGGER.severe(String.format(Beetlz.getResourceBundle().
                                      getString("JmlFile.problemWithClass"),
                                      a_symbol.className()));  //$NON-NLS-1$
        }
      } //end instanceof
    } //end annotation filter
    return null;
  }

  /**
   * Get classes.
   * @return parsed classes
   */
  public final ClassCollection getClassCollection() {
    return this.my_classCollection;
  }

  /**
   * Print to std out.
   */
  public final void printOut() {
    LOGGER.info(Beetlz.getResourceBundle().
                getString("JmlFile.javaFileContents")); //$NON-NLS-1$
    my_classCollection.printOut();
  }

  /**
   * String representation.
   * @return string representation
   */
  @Override
  public final String toString() {
    return my_classCollection.toString();
  }

  /**
   * String representation.
   * @return string representation
   */
  public final String toStringVerbose() {
    return my_classCollection.toStringVerbose();
  }

  /**
   * Gets the time when the newest file was modified.
   * @return A long value representing the time the file was last modified,
   * measured in milliseconds since the epoch (00:00:00 GMT, January 1, 1970)
   */
  public final long lastModified() {
    long time = 0;
    for (final File f : my_files) {
      if (time < f.lastModified()) {
        time = f.lastModified();
      }
    }
    return time;
  }
}
