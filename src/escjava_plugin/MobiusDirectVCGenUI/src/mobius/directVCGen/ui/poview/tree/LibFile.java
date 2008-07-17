package mobius.directVCGen.ui.poview.tree;

import java.io.File;

import mobius.directVCGen.ui.poview.util.ImagesUtils;
import mobius.directVCGen.ui.poview.util.ImagesUtils.EImages;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.graphics.Image;


public class LibFile extends UnknownFile {
  /** the name of the file when it is compiled. */
  private final File fFileVo;
  
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
