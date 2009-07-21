package mobius.bmlvcgen.util;

import java.util.Iterator;

/**
 * Various static methods operating on strings.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class StringUtil {
  /**
   * Private constructor.
   */
  private StringUtil() {
  }
  
  /**
   * Create a string with all elements of a collection
   * joined by given string.
   * To convert objects to string, toString() is used.
   * @param col Collection.
   * @param sep String inserted between collection elements.
   * @return String with collection elements separated by sep.
   */
  public static String join(final Iterable<?> col, 
                            final String sep) {
    final StringBuilder result = new StringBuilder();
    final Iterator<?> i = col.iterator();
    while (i.hasNext()) {
      result.append(i.next().toString());
      if (i.hasNext()) {
        result.append(sep);
      }
    }
    return result.toString();
  }
  
  /**
   * Concatenate two classpath strings.
   * Duplicates are not removed. Paths must
   * not be null, but can be empty.
   * @param path1 First classpath.
   * @param path2 Second classpath.
   * @return Concatenated classpaths.
   */
  public static String concatPaths(final String path1, final String path2) {
    final String separator = System.getProperty("path.separator", "");
    if (path1.trim().equals("")) {
      return path2;
    } else if (path2.trim().equals("")) {
      return path1;
    } else {
      return path1 + separator + path2;
    }
  }
  
}
