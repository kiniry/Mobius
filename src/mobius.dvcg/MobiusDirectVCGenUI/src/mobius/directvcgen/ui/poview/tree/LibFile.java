package mobius.directvcgen.ui.poview.tree;

import java.io.File;

import mobius.util.plugin.ImagesUtils.EImages;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.graphics.Image;


/**
 * Represents a vernacular file from a library.
 * If its compilation was a success its image turns violet.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class LibFile extends UnknownFile {
  /** the name of the file when it is compiled. */
  private final File fFileVo;
  
  /**
   * Construct a library node from the lib file.
   * @param file a resource representing a Coq file
   */
  LibFile(final IFile file) {
    super(file);

    final String tmp = file.getRawLocation().toString();
    fFileVo = new File(tmp + "o");
    
  }

  /** {@inheritDoc} */
  public Image getImage () {
    if (fFileVo.exists()) {
      return EImages.LIB_RED.getImg();
    }
    else {
      return EImages.LIB.getImg();
    }
  }
}
