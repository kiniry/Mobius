package input;

import ie.ucd.bon.API;
import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.parser.tracker.ParsingTracker;

import java.io.File;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;
import java.util.logging.Logger;

import main.Beetlz;
import structure.ClassCollection;
import structure.ClassStructure;
import utils.BConst;

/**
 * Collects all BON input files and the parsed class structures,
 * if available.
 * Hence, the class is responsible for storing and initialisation and
 * control of parsing with the help of BONc.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class BonFile {
  /** Input files.  */
  private final List < File > my_files;
  /** Parsed classes.  */
  private final ClassCollection my_classCollection;
  /** BON parser.  */
  private final BONWalker my_bonWalker;
  /** Our Logger for this session.  */
  private static final Logger LOGGER = Logger.getLogger(BConst.LOGGER_NAME);


  /**
   * Creates a new empty container for BON files..
   */
  public BonFile() {
    my_classCollection = new ClassCollection();
    my_files = new Vector < File > ();
    my_bonWalker = new BONWalker();
  }

  /**
   * Add a file.
   * @param some_file_names list of input file names
   */
  public final void addFiles(final List < String > some_file_names) {

    for (final String s : some_file_names) {
      final File temp = new File(s);
      if (!my_files.contains(temp)) { //ignore duplicate files
        if (temp.exists()) {
          LOGGER.config("Adding BON file " + //$NON-NLS-1$
                        s + ".");  //$NON-NLS-1$
          my_files.add(temp);
        } else {
          LOGGER.severe("Cannot find file " + s); //$NON-NLS-1$
        }
      }
    }
  }

  /**
   * Parse classes.
   * @return true if successful
   */
  public final boolean parseAll() {
    boolean parse_success = true;
    if (my_files.size() == 0) {
      return true;
    }
    
    ParsingTracker tracker = API.parse(my_files, false, false);

    if (tracker.getErrorsAndWarnings().getNumberOfErrors() == 0) {
      LOGGER.config("Successfully compiled BON files."); //$NON-NLS-1$
      my_bonWalker.parseTypingInformation(tracker);
      my_classCollection.addMoreClasses(my_bonWalker.getAllClasses());
    } else {
      System.out.println("BONc parsing failed.");
      Iterator<BONProblem> i = tracker.getErrorsAndWarnings().getProblems().iterator();
      while(i.hasNext()) {
        BONProblem problem = i.next();
        System.out.println(problem.getLocation());
        System.out.println(problem.getMessage());
        
      }
      parse_success = false;
    }
    return parse_success;
  }

  /**
   * Print to std out.
   */
  /*public final void printOut() {
    LOGGER.info("BON file contents:"); //$NON-NLS-1$
    my_classCollection.printOut();

  }*/

  /**
   * Get classes.
   * @return parsed classes
   */
  public final ClassCollection getClassCollection() {
    return this.my_classCollection;
  }

  /**
   * String representation.
   * @see java.lang.Object#toString()
   * @return string representation
   */
  @Override
  public final String toString() {
    String str = "parsed Bon classes: [";
    for(ClassStructure c: my_classCollection.getClasses()){
      str += c.getSimpleName() + ", ";
    }
    if(str.length() > 2)
      str = str.substring(0, str.length() -2) + "]";
    return str;
  }


  /**
   * String representation.
   * @return string representation
   */
  /*public final String toStringVerbose() {
    return my_classCollection.toStringVerbose();
  }*/

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
