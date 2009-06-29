package mobius.bicolano;

import java.io.IOException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;

public class BicolanoUtil {
  public static String getBicolanoPath() {
    final URL url = Activator.getDefault().getBundle().getResource("/lib/bicolano.jar");
    try {
      return FileLocator.toFileURL(url).getPath();
    } catch (IOException e) {
      return null;
    }
  }
}
