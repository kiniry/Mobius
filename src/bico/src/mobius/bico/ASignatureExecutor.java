package mobius.bico;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;

import mobius.bico.Util.Stream;

public abstract class ASignatureExecutor extends ABasicExecutor {

  Stream fOutSig;
  public ASignatureExecutor(ASignatureExecutor be) {
    super(be);
    fOutSig = be.fOutSig;
  }
  public ASignatureExecutor(ABasicExecutor be,
                            final File workingDir, 
                            final ClassGen cg) throws FileNotFoundException  {
    super(be);
    final File strm = determineStrmFileName(workingDir, cg);
    fOutSig = new Util.Stream(new FileOutputStream(new File(workingDir, strm.getPath())));
  }
  
  private static File determineStrmFileName(final File workingDir, final ClassGen clzz) {
    final JavaClass jc = clzz.getJavaClass(); 
    final File dir = new File(jc.getPackageName().replace('.', File.separatorChar));
    new File(workingDir, dir.getPath()).mkdirs();
    return new File(dir, Util.coqify(jc.getClassName()) + "_signature" + ".v");
  }
  public abstract void doSignature() throws ClassNotFoundException;
  
}
