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
public class Z3Activator extends AbstractUIPlugin {

  /** The plug-in ID. */
  public static final String PLUGIN_ID = "mobius.atp.z3";

  /** The shared instance. */
  private static Z3Activator plugin;

  public static String [][] z3Binaries = {
    {"Linux", "z3 2.0 for Linux (using wine)", "Z3-2.0/bin/z3.sh"},                            
    {"Windows", "z3 2.0 for Windows", "Z3-2.0/bin/z3.exe"},
    {"WindowsMt", "z3 2.0 MT for Windows", "Z3-2.0/bin_mt/z3.exe"},
    {"Windows64","z3 2.0_64bits for Windows", "Z3-2.0/x64/z3.exe"},
    {"windows64Mt", "z3 2.0_64bit MT for Windows", "Z3-2.0/x64_mt/z3.exe"}};
  
  private static final Map<String, ProverPath> z3s = new HashMap<String, ProverPath>();
  /**
   * The constructor.
   */
  public Z3Activator() {
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
  public static Z3Activator getDefault() {
    return plugin;
  }
  
  
  /**
   * Finds the simplify executable that is part of the the plugin.
   * @param os The name of the OS
   * @return The location of the simplify executable as an absolute file system path.
   * @throws Exception
   */
  public static String findInternalZ3(String os) throws Exception {
    if (os == null || os.length() == 0) {
      os = System.getProperty("os.name");
    }
    ProverPath res = z3s.get(os);
    if (res == null) {
      String [] name = getZ3(os);
      String executable = Utils.findPluginResource(PLUGIN_ID, name[2]);
      res = new ProverPath(name[1], executable);
      res.mkExecutable();
      z3s.put(os, res);
    }
    return res.getPath();
  }
  
  public static String  [] getZ3(String osname) {
    String os = osname.toLowerCase().trim();
    String [] res = null;
    if (os.startsWith("linux")) {
      res = z3Binaries[0];
    }
    if (os.startsWith("windows")) {
      res = z3Binaries[1];
    }
    else Log.log("Unexpected OS: " + osname);
    return res;
  }
  
  public static ProverPath[] getZ3List() {
    ProverPath [] pp = new ProverPath[z3Binaries.length];
    for (int i = 0; i < pp.length; i++) {
      String [] curr = z3Binaries[i];
      try {
        pp[i] = z3s.get(curr[0]);
        if (pp[i] == null) {
          pp[i] = new ProverPath(curr[1], 
                               Utils.findPluginResource(PLUGIN_ID, curr[2]));
          try {
            pp[i].mkExecutable();
          } 
          catch (IOException e) { 
          }
          z3s.put(curr[0], pp[i]);
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

