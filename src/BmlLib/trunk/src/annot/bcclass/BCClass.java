package annot.bcclass;

import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;

import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.Parsing;

/**
 * This class contains the full functionality of a BML class. It allows to
 * access its structure, save and load class data from a class file,
 * pretty print its content, and parse textual representations.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BCClass extends BCClassPrinting {

  /**
   * A set of functions for parsing annotations.
   */
  private Parsing parser;

  /**
   * A constructor from already existing JavaClass. That
   * JavaClass should be used for operations on byte code
   * using the BCEL library.
   *
   * @param ajc - JavaClass representing byte code class
   *     this class should operate on.
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  public BCClass(final JavaClass ajc) throws ReadAttributeException {
    this.parser = new Parsing(this);
    load(ajc);
  }

  /**
   * A constructor from a .class file. It loads JavaClass
   * from that file (using BCEL) first, then loads BML
   * annotations from it. Don't forget to get JavaClass
   * from constructed object (getJC() method), instead of
   * creating a new instance of JavaClass using BCEL.
   *
   * @param dirName - path of directory where .class file
   *     is located, excluding directories included
   *     in <code>className</code>,
   * @param className - package and class name of class that
   *     should be loaded. For example, constructor call:
   *     BCClass("C:\\workspace\\Project\\", "test.aclass");
   *     searches for file:
   *     C:\workspace\Project\test\aclass.class,
   * @throws ClassNotFoundException - iff .class file
   *     could not be found,
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  public BCClass(final String dirName, final String className)
    throws ClassNotFoundException, ReadAttributeException {
    MLog.putMsg(MessageLog.LEVEL_PINFO, "filename=" + dirName);
    MLog.putMsg(MessageLog.LEVEL_PINFO, "className=" + className);
    final ClassPath acp = new ClassPath(dirName);
    SyntheticRepository.getInstance(acp).clear();
    final JavaClass ajc = SyntheticRepository.getInstance(acp)
        .loadClass(className);
    this.parser = new Parsing(this);
    load(ajc);
  }

  /**
   * @return object used for parsing BML annotations.
   */
  public Parsing getParser() {
    return this.parser;
  }

  /**
   * Creates a fresh BMLLib attribute reader. The actual implementation just
   * calls the constructor with class representation which has full
   * functionality.
   *
   * @return the BMLLib attribute reader
   * @see BCClassRepresentation#getFreshAttributeReader()
   */
  protected AttributeReader getFreshAttributeReader() {
    return new AttributeReader(this);
  }

  /**
   * Creates the BMLLib representation of the given method in the class of the
   * given name and with the given constant pool. This method creates
   * the BML method representation which parses the BML related method
   * attributes. It also assigns fresh copies of the given constant pool
   * to the newly created method.
   *
   * @param meth the BCEL method based on which the BMLLib method is generated
   * @param clname the name of the class in which the method is located
   * @param cpool the constant pool
   * @return the BMLLib method representation
   * @throws ReadAttributeException in case some of the BML attributes wasn't
   *   correctly parsed by BMLLib
   * @see BCClassRepresentation#getFreshMethod(Method, String, ConstantPool)
   */
  protected BCMethod getFreshMethod(final Method meth,
                                    final String clname,
                                    final ConstantPool cpool)
    throws ReadAttributeException {
    return new BCMethod(this, new MethodGen(meth, clname,
      new ConstantPoolGen(cpool)));
  }
}
