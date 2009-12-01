package mobius.atp;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import mobius.util.plugin.Log;
import mobius.util.plugin.Utils;
import mobius.util.plugin.Utils.ProverPath;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;


/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Cvc3Activator extends AbstractUIPlugin {

  /** The plug-in ID. */
  public static final String PLUGIN_ID = "mobius.atp.cvc3";

  /** The shared instance. */
  private static Cvc3Activator plugin;

  public static String [][] cvc3Binaries = {
    {"Linux32", "Cvc3 for linux 32bits", "cvc3-optimized-linux-32"},
    {"Linux64", "Cvc3 for linux 64bits", "cvc3-optimized-linux-64"}};
  
  private static final Map<String, ProverPath> cvc3 = new HashMap<String, ProverPath>();
  /**
   * The constructor.
   */
  public Cvc3Activator() {
    plugin = this;
    
  }

  /** {@inheritDoc} */
  public void start(final BundleContext context) throws Exception {
    super.start(context);

  }

  public static void loadCvc3Thingie() {
    try {
      String javapath = "cvc3-20090730/java/lib/";
      String path = "cvc3-20090730/lib/";
      String [] libnames = {"libcvc3.so.1", "libcvc3.so.1.0", "libcvc3.so.1.0.0", "libcvc3.so"};
      String [] libjavanames = {"libcvc3jni.so.1", "libcvc3jni.so.1.0", "libcvc3jni.so.1.0.0", "libcvc3jni.so"};
      for (String libname:libnames) {
        System.load(Utils.findPluginResource(PLUGIN_ID, path + libname));
      }
      for (String libname:libjavanames) {
        System.load(Utils.findPluginResource(PLUGIN_ID, javapath + libname));
      }


      System.mapLibraryName("cvc3jni");
      System.mapLibraryName("cvc3");
      
    } catch (Throwable e) {
      e.printStackTrace();
    }
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
  public static Cvc3Activator getDefault() {
    return plugin;
  }
  
  
  /**
   * Finds the cvc3 executable that is part of the the plugin.
   * @param os The name of the OS
   * @return The location of the cvc3 executable as an absolute file system path.
   * @throws Exception
   */
  public static String findInternalCvc3(String os) throws Exception {
    if (os == null || os.length() == 0) {
      os = System.getProperty("os.name");
    }
    ProverPath res = cvc3.get(os);
    if (res == null) {
      String [] name = getCvc3(os);
      String executable = Utils.findPluginResource(PLUGIN_ID, name[2]);
      res = new ProverPath(name[1], executable);
      res.mkExecutable();
      cvc3.put(os, res);
    }
    return res.getPath();
  }
  
  public static String  [] getCvc3(String osname) {
    String os = osname.toLowerCase().trim();
    String [] res = null;
    if (os.equals("linux")) {
      res = cvc3Binaries[0];
    }
    else Log.log("Unexpected OS: " + osname);
    return res;
  }
  
  public static ProverPath[] getCvc3List() {
    ProverPath [] pp = new ProverPath[cvc3Binaries.length];
    for (int i = 0; i < pp.length; i++) {
      String [] curr = cvc3Binaries[i];
      try {
        pp[i] = cvc3.get(curr[0]);
        if (pp[i] == null) {
          pp[i] = new ProverPath(curr[1], 
                               Utils.findPluginResource(PLUGIN_ID, curr[2]));
          try {
            pp[i].mkExecutable();
          } 
          catch (IOException e) { 
          }
          cvc3.put(curr[0], pp[i]);
        }
      } 
      catch (IOException e) {
        Log.log("Unable to find the executable: " + curr[2]);
        e.printStackTrace();
      }
      
    }
    return pp;
  }
}

