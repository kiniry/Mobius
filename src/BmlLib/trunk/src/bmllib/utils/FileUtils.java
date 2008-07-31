package bmllib.utils;

import annot.textio.Parsing;

public class FileUtils {


  /**
   * A method to convert the universal path representation
   * ("/" separates the path segments) to the local operating
   * system specific one.
   *
   * @param fileName the path in the universal representation
   * @return the path in the local operating system representation
   */
  public static String toOsSpecificName(final String fileName) {
    final String filesep = System.getProperty("file.separator");
    return fileName.replaceAll("/", Parsing.escape(filesep));
  }

}
