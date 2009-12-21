package ie.ucd.bon.plugin.util;

import java.net.URL;

import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

import freemarker.cache.URLTemplateLoader;

public class EclipsePluginURLTemplateLoader extends URLTemplateLoader {

  private final Bundle bundle;
  private final String prefixPath;
  
  public EclipsePluginURLTemplateLoader(String pluginId, String prefixPath) {
    bundle = Platform.getBundle(pluginId);
    this.prefixPath = prefixPath;
  }
  
  @Override
  protected URL getURL(String name) {
    return bundle.getEntry(prefixPath + name);
  }

}
