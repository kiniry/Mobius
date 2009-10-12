package input;

import ie.ucd.bon.API;
import ie.ucd.bon.parser.tracker.ParsingTracker;

import java.io.File;
import java.util.List;
import java.util.Vector;
import java.util.logging.Logger;

import main.Beetlz;
import structure.ClassCollection;
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
          LOGGER.config(Beetlz.getResourceBundle().
                        getString("BonFile.addingBonFile") + //$NON-NLS-1$
                        s + ".");  //$NON-NLS-1$
          my_files.add(temp);
        } else {
          LOGGER.severe(Beetlz.getResourceBundle().
                        getString("BonFile.cannotFindFile") + s); //$NON-NLS-1$
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
    final List < String > args = new Vector < String > ();
    
    ParsingTracker tracker = API.parse(my_files, false, false);

    if (tracker.getErrorsAndWarnings().getNumberOfErrors() == 0) {
      LOGGER.config(Beetlz.getResourceBundle().getString("BonFile.successfullyCompiled")); //$NON-NLS-1$
      my_bonWalker.parseTypingInformation(tracker);
      my_classCollection.addMoreClasses(my_bonWalker.getAllClasses());
    } else {
      System.out.println("BONc parsing failed.");
      parse_success = false;
    }
    return parse_success;
  }

  /**
   * Print to std out.
   */
  public final void printOut() {
    LOGGER.info(Beetlz.getResourceBundle().getString("BonFile.bonFiles")); //$NON-NLS-1$
    my_classCollection.printOut();

  }

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
