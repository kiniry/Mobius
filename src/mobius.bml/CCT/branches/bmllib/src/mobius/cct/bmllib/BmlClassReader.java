package mobius.cct.bmllib;

import java.io.IOException;
import java.io.InputStream;

import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.JavaClass;

import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;

import mobius.cct.classfile.ClassReader;

/**
 * Reader for BML class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class BmlClassReader 
  implements ClassReader<BmlClassFile> {

  /** {@inheritDoc} */
  @Override
  public BmlClassFile read(final InputStream is) 
    throws IOException {
    final ClassParser parser = new ClassParser(is, null);
    final JavaClass jc = parser.parse();
    final BCClass clazz;
    try {
      clazz = new BCClass(jc);
    } catch (final ReadAttributeException e) {
      throw new IOException(e);
    }
    return new BmlClassFile(clazz);
  }

}
