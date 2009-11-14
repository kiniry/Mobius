package ie.ucd.bon.plugin.util;

public class PluginUtil {

  private static final boolean IS_WINDOWS = System.getProperty("os.name").toLowerCase().contains("win");
  private static final boolean IS_MAC = System.getProperty("os.name").toLowerCase().startsWith("mac os x");
  
  public static int eclipseAbsoluteCharacterPosition(int absolutePosition, int lineNumber) {
    //Adjusting for different counting of line-ending characters between eclipse and antlr
    if ((IS_WINDOWS || IS_MAC) && lineNumber != -1) {
      return absolutePosition + (lineNumber - 1);
    } else {
      return absolutePosition;
    }
  }
  
}
