package ie.ucd.gf;

public class SystemUtil {

  private static final String OS_NAME_PROP_NAME = "os.name";
  private static final String OS_NAME = System.getProperty(OS_NAME_PROP_NAME) == null ? "" : System.getProperty(OS_NAME_PROP_NAME);
  
  public static final boolean IS_OS_LINUX = OS_NAME.startsWith("Linux") || OS_NAME.startsWith("LINUX");
  public static final boolean IS_OS_MAC = OS_NAME.startsWith("Mac");
  public static final boolean IS_OS_MAC_OSX = OS_NAME.startsWith("Mac OS X");
  public static final boolean IS_OS_WINDOWS = OS_NAME.startsWith("Windows");
  
  private static final String OS_ARCH_PROP_NAME = "os.arch";
  private static final String OS_ARCH = System.getProperty(OS_ARCH_PROP_NAME) == null ? "" : System.getProperty(OS_ARCH_PROP_NAME);

  public static final boolean IS_OS_LINUX_32 = IS_OS_LINUX && OS_ARCH.startsWith("i386");
  public static final boolean IS_OS_LINUX_64 = IS_OS_LINUX && OS_ARCH.startsWith("amd64");
  
}
