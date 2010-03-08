package ie.ucd.bon.plugin.util;

import ie.ucd.bon.util.StringUtil.VersionProvider;

import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;
import org.osgi.framework.Version;

public class EclipsePluginVersionProvider implements VersionProvider {
  
  private final Bundle bundle;
  
  public EclipsePluginVersionProvider(String pluginId) {
    bundle = Platform.getBundle(pluginId);
  }
  
  public String getVersion() { 
    if (bundle != null) {
      Version version = bundle.getVersion();
      return "BONc Eclipse plugin " + version.toString();
    }
    return null;
  }
}