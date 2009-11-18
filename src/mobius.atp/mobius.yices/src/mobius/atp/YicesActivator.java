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
public class YicesActivator extends AbstractUIPlugin {

  /** The plug-in ID. */
  public static final String PLUGIN_ID = "mobius.atp.yices";

  /** The shared instance. */
  private static YicesActivator plugin;


  public static String [][] yicesBinaries = {
	  
    {"Windows", "Yices 1.0.21 for cygwin", "yices-1.0.21-i686-pc-cygwin.exe"},
    {"Linux", "Yices 1.0.21 for Linux i686", "yices-1.0.21-i686-pc-linux-gnu"},
    {"Solaris","Yices 1.0.21 for Solaris", "yices-1.0.21-sparc-sun-solaris2.10"},
    {"mingw32", "Yices 1.0.21 for mingw32", "yices-1.0.21-i686-pc-mingw32.exe"},
    {"MacOSX", "Yices 1.0.21 for MacOS X Darwin 9.6.0 i386", "yices-1.0.21-i386-apple-darwin9.6.0"},
    {"Linux64", "Yices 1.0.21 for Linux x86_64", "yices-1.0.21-x86_64-pc-linux-gnu"},
    {"MacOSX8.11", "Yices 1.0.21 for MacOS X Darwin 8.11.1 i386", "yices-1.0.21-i386-apple-darwin8.11.1"},
    {"MacOSX8.11ppc", "Yices 1.0.21 for MacOS X Darwin 8.11.0 powerpc", "yices-1.0.21-powerpc-apple-darwin8.11.0"},
    {"MacOSX9.6_64", "Yices 1.0.21 for MacOS X Darwin 9.6.0 x86_64", "yices-1.0.21-x86_64-apple-darwin9.6.0"}
  };
  
  private static final Map<String, ProverPath> yices = new HashMap<String, ProverPath>();
  /**
   * The constructor.
   */
  public YicesActivator() {
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
  public static YicesActivator getDefault() {
    return plugin;
  }
  
  
  /**
   * Finds the simplify executable that is part of the the plugin.
   * @param os The name of the OS
   * @return The location of the simplify executable as an absolute file system path.
   * @throws Exception
   */
  public static String findInternalYices(String os) throws Exception {
    if (os == null || os.length() == 0) {
      os = System.getProperty("os.name");
    }
    ProverPath res = yices.get(os);
    if (res == null) {
      String [] name = getYices(os);
      String executable = Utils.findPluginResource(PLUGIN_ID, name[2]);
      res = new ProverPath(name[1], executable);
      res.mkExecutable();
      yices.put(os, res);
    }
    return res.getPath();
  }
  
  public static String  [] getYices(String osname) {
    String os = osname.toLowerCase().trim();
    String [] res = null;
    if (os.startsWith("windows")) {
      res = yicesBinaries[0];
    }
    else if (os.equals("linux")) {
      res = yicesBinaries[1];
    }
    else if (os.equals("darwin")||
             os.equals("macosx")||
             os.equals("mac os x")) {
      res = yicesBinaries[4]; 
    }
    else if (os.equals("solaris")) {
      res = yicesBinaries[2]; 
    }
    else if (os.equals("mingw32")) {
      res = yicesBinaries[3]; 
    }
    else if (os.equals("darwin")||
        os.equals("macosx")||
        os.equals("mac os x")) {
      res = yicesBinaries[4]; 
    }
    else Log.log("Unexpected OS: " + osname);
    return res;
  }
  
  public static ProverPath[] getYicesList() {
    ProverPath [] pp = new ProverPath[yicesBinaries.length];
    for (int i = 0; i < pp.length; i++) {
      String [] curr = yicesBinaries[i];
      try {
        pp[i] = yices.get(curr[0]);
        if (pp[i] == null) {
          pp[i] = new ProverPath(curr[1], 
                               Utils.findPluginResource(PLUGIN_ID, curr[2]));
          try {
            pp[i].mkExecutable();
          } 
          catch (IOException e) { 
          }
          yices.put(curr[0], pp[i]);
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

