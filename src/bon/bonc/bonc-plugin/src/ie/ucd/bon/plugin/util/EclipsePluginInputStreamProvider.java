package ie.ucd.bon.plugin.util;

import ie.ucd.bon.util.FileUtil.InputStreamProvider;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;

import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

public class EclipsePluginInputStreamProvider implements InputStreamProvider {
  
  private final Bundle bundle;
  
  public EclipsePluginInputStreamProvider(String pluginId) {
    bundle = Platform.getBundle(pluginId);
  }
  
  public InputStream getInputStream(String filePath) { 
    if (bundle != null) {
      URL url = bundle.getEntry(filePath);
      if (url != null) {
        try {
          return url.openStream();
        } catch (IOException e) {
          e.printStackTrace();
          return null;
        }
      }
    }
    return null;
  }
}