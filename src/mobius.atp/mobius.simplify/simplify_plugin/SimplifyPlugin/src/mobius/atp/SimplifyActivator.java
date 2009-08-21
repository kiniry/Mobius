package mobius.atp;

import java.io.IOException;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import pluginlib.Log;
import pluginlib.Utils;
import pluginlib.Utils.ProverPath;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class SimplifyActivator extends AbstractUIPlugin {

  /** The plug-in ID. */
  public static final String PLUGIN_ID = "mobius.atp.simplify";

  /** The shared instance. */
  private static SimplifyActivator plugin;

  public static String [][] simplifyBinaries = {
    {"Windows", "Simplify 1.5.4 for Windows", "Simplify-1.5.4.exe"},
    {"Linux", "Simplify 1.5.4 for Linux", "Simplify-1.5.4.linux"},
    {"Solaris","Simplify 1.5.4 for Solaris", "Simplify-1.5.4.solaris"},
    {"tru64", "Simplify 1.5.4 for tru64", "Simplify-1.5.4.tru64"},
    {"MacOSX", "Simplify 1.5.5 for MacOS X", "Simplify-1.5.5.macosx"},
  };
  
  
  /**
   * The constructor.
   */
  public SimplifyActivator() {
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
  public static SimplifyActivator getDefault() {
    return plugin;
  }
  
  
  /**
   * Finds the simplify executable that is part of the the plugin.
   * @param os The name of the OS
   * @return The location of the simplify executable as an absolute file system path.
   * @throws Exception
   */
  public static String findInternalSimplify(String os) throws Exception {
    if (os == null || os.length() == 0) {
      os = System.getProperty("os.name");
    }
    String [] name = getSimplify(os);
    String executable = Utils.findPluginResource(PLUGIN_ID, name[2]);
    return executable;
  }
  
  public static String  [] getSimplify(String osname) {
    String os = osname.toLowerCase().trim();
    String [] res = null;
    if (os.startsWith("windows")) {
      res = simplifyBinaries[0];
    }
    else if (os.equals("linux")) {
      res = simplifyBinaries[1];
    }
    else if (os.equals("darwin")||
             os.equals("macosx")||
             os.equals("mac os x")) {
      res = simplifyBinaries[4]; 
    }
    else if (os.equals("solaris")) {
      res = simplifyBinaries[2]; 
    }
    else if (os.equals("tru64")) {
      res = simplifyBinaries[3]; 
    }
    else if (os.equals("darwin")||
        os.equals("macosx")||
        os.equals("mac os x")) {
      res = simplifyBinaries[4]; 
    }
    else Log.log("Unexpected OS: " + osname);
    return res;
  }
  
  public static ProverPath[] getSimplifyList() {
    ProverPath [] pp = new ProverPath[simplifyBinaries.length];
    for (int i = 0; i < pp.length; i++) {
      String [] curr = simplifyBinaries[i];
      try {
        pp[i] = new ProverPath(curr[1], 
                               Utils.findPluginResource(PLUGIN_ID, curr[2]));
      } catch (IOException e) {
        Log.log("Unable to find the executable: " + curr[2]);
        e.printStackTrace();
      }
    }
    return pp;
  }
}

