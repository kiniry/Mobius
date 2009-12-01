package mobius.escjava2;


import mobius.atp.Cvc3Activator;
import mobius.util.plugin.Utils;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;


/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class EscToolsActivator extends AbstractUIPlugin {

  /** The plug-in ID. */
  public static final String PLUGIN_ID = "mobius.escjava2.esctools";

  /**
   * Name of jarfile of ESC/Java2 build (has been "esctools2.jar" for a *long* time).
   */
  public static final String ESCJAVA_JAR_FILENAME = "esctools2.jar";
  

  public enum JavaVersions {
    DEFAULT("Default", "escspecs.jar"),
    JAVA_CARD_2_1("JavaCard 2.1", "escspecs-javacard.jar"),
    JAVA_1_3("1.3",  "escspecs-java1.4.jar"),
    JAVA_1_4("1.4",  "escspecs-java1.4.jar"),
    JAVA_1_5("1.5",  "escspecs-java1.5.jar"),
    JAVA_1_6("1.6",  "escspecs-java1.6.jar");
    
    
    private final String str;
    private final String specs;
    public String toString() {
      return str;
    }
    public String getSpecsJarfileName() {
      return specs;
    }
    
    private JavaVersions(final String str, final String specs) {
      this.str = str;
      this.specs = specs;
    }
    public static String [] toStringList() {
      JavaVersions [] jvs = JavaVersions.values();
      String [] res = new String [jvs.length];
      
      for (int i = 0; i < res.length; i++) {
        res[i] = jvs[i].toString();
      }
      return res;
    }
    
    public static boolean isValidSpecsJar(String location) {
      for (JavaVersions jv: JavaVersions.values()) {
        if (location.endsWith(jv.specs)) {
          return true;
        }
      }
      return false;
    }
    
    public static JavaVersions selected(String val) {
      for (JavaVersions jv: JavaVersions.values()) {
        if (jv.str.equals(val)) {
          return jv;
        }
      }
      return DEFAULT;
    }
  }
  /** The shared instance. */
  private static EscToolsActivator plugin;

  
  
  /**
   * The constructor.
   */
  public EscToolsActivator() {
    plugin = this;
  }

  /** {@inheritDoc} */
  public void start(final BundleContext context) throws Exception {
    super.start(context);
  }

  /** {@inheritDoc} */
  public void stop(final BundleContext context) throws Exception {
    super.stop(context);
    
  }

  /**
   * Returns the shared instance.
   *
   * @return the shared instance
   */
  public static EscToolsActivator getDefault() {
    return plugin;
  }
  public static void loadCvc3Thingie() {
    Cvc3Activator.loadCvc3Thingie();
    try {
      String path = "";
      String [] libnames = {"libcvc3jniw.so"};
      for (String libname:libnames) {
        System.load(Utils.findPluginResource(PLUGIN_ID, path + libname));
      }


      System.mapLibraryName("cvc3jniw");
      
    } catch (Throwable e) {
      e.printStackTrace();
    }
  }

}

