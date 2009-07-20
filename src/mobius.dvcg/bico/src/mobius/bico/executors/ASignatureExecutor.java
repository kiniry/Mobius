package mobius.bico.executors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;

import mobius.bico.Util;
import mobius.bico.bicolano.coq.CoqStream;

/**
 * An abstract class used to add signature handling to 
 * the executors.
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class ASignatureExecutor extends ABasicExecutor {
  /** the stream where to write the things which concern the signature. */
  final CoqStream fOutSig;
  
  
  /**
   * Construct a signature executor from an already existing 
   * one. All the fields from the existing are copied.
   * @param se the old signature executor
   */
  public ASignatureExecutor(final ASignatureExecutor se) {
    super(se);
    fOutSig = se.fOutSig;
  }
  
  /**
   * Build a signature executor from a basic executor;
   * and initialize its fields from the given arguments.
   * @param be the old basic executor to copy some fields from
   * @param cg the current treated class
   * @throws FileNotFoundException if the creation of the stream fails
   */
  public ASignatureExecutor(final ABasicExecutor be,
                            final ClassGen cg) throws FileNotFoundException  {
    super(be);
    setBaseDir(new File(be.getBaseDir(), 
                        File.separator + "classes"));
    getBaseDir().mkdirs();
    
    final File strm = determineStrmFileName(getBaseDir(), cg);
    fOutSig = new CoqStream(new FileOutputStream(strm));
    
  }
  
  /**
   * Determine the file name for the signature file
   * from the current base dir and 
   * the current class.
   * @param workingDir the current base directory
   * @param clzz the class to get the name from
   * @return a valid file
   */
  private static File determineStrmFileName(final File workingDir, final ClassGen clzz) {
    final JavaClass jc = clzz.getJavaClass(); 
    final File dir = new File(workingDir, 
                              jc.getPackageName().replace('.', 
                                                          File.separatorChar));
    dir.getAbsoluteFile().mkdirs();
    return new File(dir, Util.coqify(jc.getClassName()) + "_signature" + ".v");
  }
  
  /**
   * The method to call to generate the signature to the given stream.
   * @throws ClassNotFoundException if there is an error while retrieving
   * a field or a method
   */
  public abstract void doSignature() throws ClassNotFoundException;
  
}
