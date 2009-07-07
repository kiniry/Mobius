package main;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.logging.Logger;

import utils.BConst;

/**
 * Reads in custom settings from a file and inserts the information where we
 * want it and how we want it.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 * TODO: maybe do this with a properties file and resource bundle (test feasibility)
 */
public final class SettingIO {

  /** */
  private SettingIO() { }

  /** Our Logger for this session. */
  private static final Logger LOGGER =
    Logger.getLogger(BConst.LOGGER_NAME);

  /**
   * Read in a custom user file and put the information in the user profile.
   * @param a_profile user profile, hold the file name of the custom file,
   * will be written into with new information as well
   * @param a_filename file name to read from
   * @return true if successfull
   */
  public static boolean readSettings(final UserProfile a_profile,
                                     final String a_filename) {

    if (a_filename.length() == 0) { //no user file specified
      return true;
    }
    final File temp = new File(a_filename);
    FileReader fr;
    BufferedReader br;
    try {
      fr = new FileReader(temp);
      br = new BufferedReader(fr);
    } catch (final FileNotFoundException e) {
      LOGGER.severe(String.format(Beetlz.getResourceBundle()
          .getString("SettingIO.customSettingsFileNotFound"), //$NON-NLS-1$
                                  a_filename));
      return false;
    }

    try {
      String line = ""; //$NON-NLS-1$
      String s;
      while ((s = br.readLine()) != null) {
        if (!s.startsWith("--")) { //$NON-NLS-1$
          line += s.trim();
        }
        //ends with semicolon, process it
        if (s.trim().endsWith(";")) { //$NON-NLS-1$
          processLine(line.trim(), a_profile);
          line = ""; //$NON-NLS-1$
        }
      }
      if (!line.equals("")) { //$NON-NLS-1$
        LOGGER.severe(String.format(Beetlz.getResourceBundle()
            .getString("SettingIO.customFileSyntaxError"), //$NON-NLS-1$
                                    line));
      }
    } catch (final IOException exc) {
      LOGGER.severe(Beetlz.getResourceBundle().
                    getString("SettingIO.errorReadingFile")); //$NON-NLS-1$
      exc.printStackTrace();
      return false;
    }

    try {
      fr.close();
    } catch (final IOException exc) {
      LOGGER.severe(Beetlz.getResourceBundle()
          .getString("SettingIO.cannotCloseSettingsFile")); //$NON-NLS-1$
      return false;
    }

    return true;
  }

  /* ****************************
   * Private methods
   ******************************/

  /**
   * Process one line of the input.
   * @param a_line the line to process
   * @param a_profile user profile
   */
  private static void processLine(final String a_line,
                                  final UserProfile a_profile) {
    final String trimmedLine = a_line.trim();
    //type: comment
    if (!(trimmedLine.startsWith("--") || a_line.equals(""))) { //$NON-NLS-1$ //$NON-NLS-2$
      //type: class_mapping
      if (trimmedLine.startsWith("class_mapping")) { //$NON-NLS-1$
        processClassMapping(trimmedLine, a_profile);
      //type: feature_mapping
      } else if (trimmedLine.startsWith("feature_mapping")) { //$NON-NLS-1$
        processFeatureMapping(trimmedLine, a_profile);
      //type: type_mapping
      } else if (trimmedLine.startsWith("type_mapping")) { //$NON-NLS-1$
        processTypeMapping(trimmedLine, a_profile);
      //type: ignore_classes
      } else if (trimmedLine.startsWith("ignore_classes")) { //$NON-NLS-1$
        processIgnoreClasses(trimmedLine, a_profile);
      //type: ignore_prefix
      } else if (trimmedLine.startsWith("ignore_prefix")) { //$NON-NLS-1$
        processIgnorePrefix(trimmedLine, a_profile);
      } else {
        LOGGER.severe(String.format(Beetlz.getResourceBundle()
            .getString("SettingIO.customFileSyntaxError"), //$NON-NLS-1$
                                    a_line));
      }
    }
  }

  /**
   * Process a class mapping.
   * @param a_line line to process
   * @param a_profile uer profile
   */
  private static void processClassMapping(final String a_line,
                                          final UserProfile a_profile) {
    final int two = 2;
    final int three = 3;
    String[] parts;
    if (a_line.endsWith(";")) { //$NON-NLS-1$
      parts = a_line.substring(0, a_line.length() - 1).split(" "); //$NON-NLS-1$
    } else {
      parts = a_line.split(" "); //$NON-NLS-1$
    }
    if (parts[0].equals("class_mapping") && //$NON-NLS-1$
        parts.length == three) { //correct beginning
      a_profile.addClassMapping(parts[1], parts[two]);
    } else {
      LOGGER.severe(String.format(Beetlz.getResourceBundle()
          .getString("SettingIO.syntaxErrorClassMapping"), //$NON-NLS-1$
                                  a_line));
    }
  }

  /**
   * Process a feature mapping.
   * @param a_line line to process
   * @param a_profile uer profile
   */
  private static void processFeatureMapping(final String a_line,
                                            final UserProfile a_profile) {
    String[] parts;
    final int two = 2;
    final int three = 3;
    if (a_line.endsWith(";")) { //$NON-NLS-1$
      parts = a_line.substring(0, a_line.length() - 1).split(" "); //$NON-NLS-1$
    } else {
      parts = a_line.split(" "); //$NON-NLS-1$
    }

    if (parts[0].equals("feature_mapping") &&
        parts.length == three) { //correct beginning //$NON-NLS-1$
      a_profile.addFeatureMapping(parts[1], parts[two]);
    } else {
      LOGGER.severe(String.format(Beetlz.getResourceBundle()
          .getString("SettingIO.syntaxErrorFeatureMapping"), //$NON-NLS-1$
                                  a_line));
    }
  }

  /**
   * Process a feature mapping.
   * @param a_line line to process
   * @param a_profile uer profile
   */
  private static void processTypeMapping(final String a_line,
                                         final UserProfile a_profile) {
    final String[] parts = a_line.split("[{]"); //$NON-NLS-1$
    final int three = 3;
    final int two = 2;
    if (parts.length == three) { //correct beginning
      final String[] typeAndName = parts[0].split(" "); //$NON-NLS-1$
      final String bNames = parts[1].replaceAll("}", ""); //$NON-NLS-1$ //$NON-NLS-2$
      final String jNames = parts[two].replaceAll("}", ""); //$NON-NLS-1$ //$NON-NLS-2$
      final String[] bonTypes = bNames.split(","); //$NON-NLS-1$
      final String[] javaTypes = jNames.split(","); //$NON-NLS-1$
      if (typeAndName[0].equals("type_mapping") && typeAndName.length == two && //$NON-NLS-1$
          bonTypes.length > 0 && javaTypes.length > 0) {
        a_profile.addTypeMapping(typeAndName[1], bonTypes, javaTypes);

      } else {
        LOGGER.severe(String.format(Beetlz.getResourceBundle()
            .getString("SettingIO.customFileSyntaxError"), //$NON-NLS-1$
                                    a_line));
      }

    } else {
      LOGGER.severe(String.format(Beetlz.getResourceBundle()
          .getString("SettingIO.customFileSyntaxError"), //$NON-NLS-1$
                                  a_line));
    }
  }

  /**
   * Process an ignored classes line.
   * @param a_line line to process
   * @param a_profile uer profile
   */
  private static void processIgnoreClasses(final String a_line,
                                           final UserProfile a_profile) {
    String[] parts;
    final int three = 3;
    final int two = 2;
    if (a_line.endsWith(";")) { //$NON-NLS-1$
      parts = a_line.substring(0, a_line.length() - 1).split("[{]"); //$NON-NLS-1$
    } else {
      parts = a_line.split("[{]"); //$NON-NLS-1$
    }
    if (parts[0].trim().equals("ignore_classes") &&
        parts.length == three) { //correct beginning //$NON-NLS-1$
      final String[] ignoreBON =
        parts[1].replaceAll("[{}]", "").split(","); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
      final String[] ignoreJava =
        parts[two].replaceAll("[{}]", "").split(","); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
      a_profile.addIgnoredClasses(ignoreBON, ignoreJava);
    } else {
      LOGGER.severe(String.format(Beetlz.getResourceBundle()
          .getString("SettingIO.syntaxErrorIgnoreClasses"), //$NON-NLS-1$
                                  a_line));
    }
  }

  /**
   * Process an ignored prefixes line.
   * @param a_line line to process
   * @param a_profile uer profile
   */
  private static void processIgnorePrefix(final String a_line,
                                          final UserProfile a_profile) {
    String[] parts;
    if (a_line.endsWith(";")) { //$NON-NLS-1$
      parts = a_line.substring(0, a_line.length() - 1).split(" "); //$NON-NLS-1$
    } else {
      parts = a_line.split(" "); //$NON-NLS-1$
    }
    if (parts[0].trim().equals("ignore_prefix")) { //correct beginning //$NON-NLS-1$
      for (int i = 1; i < parts.length; i++) {
        a_profile.getPrefixes().add(parts[i]);
      }
    } else {
      LOGGER.severe(String.format(Beetlz.getResourceBundle()
          .getString("SettingIO.syntaxErrorIgnorePrefix"), //$NON-NLS-1$
                                  a_line));
    }
  }
}
