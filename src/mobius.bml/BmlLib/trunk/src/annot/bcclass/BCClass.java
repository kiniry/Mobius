/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.bcclass;

import java.util.logging.Logger;

import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;

import annot.attributes.clazz.GhostFieldsAttribute;
import annot.attributes.field.BMLModifierAttribute;
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
   * A logger to debug the current class.
   */
  private static Logger logger = Logger.getLogger("BCClass");

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
    logger.info("ctor");
    this.parser = new Parsing(this);
    final ClassGen cg = new ClassGen(ajc);
    load(cg);
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
    logger.info("ctor(" + dirName + ", " + className + ")");

    MLog.putMsg(MessageLog.LEVEL_PINFO, "filename=" + dirName);
    MLog.putMsg(MessageLog.LEVEL_PINFO, "className=" + className);
    final ClassPath acp = new ClassPath(dirName);
    SyntheticRepository.getInstance(acp).clear();
    final JavaClass ajc = SyntheticRepository.getInstance(acp)
        .loadClass(className);
    this.parser = new Parsing(this);
    final ClassGen cg = new ClassGen(ajc);
    load(cg);
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
   * @return the BMLLib method representation
   * @throws ReadAttributeException in case some of the BML attributes wasn't
   *   correctly parsed by BMLLib
   * @see BCClassRepresentation#getFreshMethod(Method, String, ConstantPool)
   */
  protected BCMethod getFreshMethod(final Method meth,
                                    final String clname)
    throws ReadAttributeException {
    return new BCMethod(this, new MethodGen(meth, clname,
                                            getCp().getConstantPool()));
  }

  /**
   * This method generates a fresh BML modifier object for the given field.
   *
   * @param field the field to generate the modifier for
   * @return a fresh modifiers structure for the field
   * @throws ReadAttributeException - if the structure of one of the field
   *   attributes is found not to be correct
   */
  protected BMLModifierAttribute getFreshFieldMod(final Field field)
    throws ReadAttributeException {
    return new BMLModifierAttribute(field, this);
  }

  /**
   * This method updates the BMLLib class inventory with the given field.
   * First it checks if the field is normal Java field or ghost or model
   * field. Then the handling is dispatched to different branches based
   * upon this choice.
   *
   * @param afield the field to update the class with
   */
  public void updateFields(final BCField afield) {
    switch (afield.getBMLKind()) {
      case BCField.JAVA_FIELD:
        updateJavaField(afield);
        break;
      case BCField.GHOST_FIELD:
        updateGhostField(afield);
        break;
      case BCField.MODEL_FIELD:
        updateModelField(afield);
        break;
      default:
        //nothing happens if unknown field kind
        break;
    }
  }

  private void updateModelField(final BCField afield) {
    // TODO make it work
  }

  /**
   * Updates the fields of the current class with a ghost BML field. It
   * looks for a ghost field of the same name first and in case of success
   * it updates the field with new information. In case of failure it adds
   * a new {@link BCField} to the ghost fields of the current class.
   *
   * @param afield to update the class representation with
   */
  private void updateGhostField(final BCField afield) {
    final GhostFieldsAttribute fds = getGhostFields();
    updateNJavaField(afield, fds);
  }

  /**
   * @param afield
   * @param fds
   */
  private void updateNJavaField(final BCField afield,
                                final GhostFieldsAttribute fds) {
    boolean found = false;
    for (int i = 0; i < fds.size(); i++) {
      final BCField fd = fds.get(i);
      if (fd != null && afield.getNameIndex() == fd.getNameIndex()) {
        fd.setAccessFlags(afield.getAccessFlags());
        final int idx = afield.getDescriptorIndex();
        fd.setDescriptorIndex(idx);
        fd.setBMLFlags(afield.getBMLFlags());
        fd.setBMLKind(afield.getBMLKind());
        found = true;
      }
    }
    if (!found) {
      //remove normal field
      removeField(afield, true);
      //remove model
      getModelFields().removeBMLField(afield);
      //remove previous ghost field of the same name
      getGhostFields().removeBMLField(afield);
      afield.setupCPEntries();
      addGhostField(afield);
    }
  }

  /**
   * Removes a normal Java field of the same name as the given one. This method
   * moves the field descriptors from the first constant pool to the second
   * one if instructed to do so. It moves the name of the field, and its
   * NameAndType descriptor. Additionally these values change in the
   * <code>afield</code> parameter.
   *
   * @param afield the field to remove from the class
   * @param b <code>true</code> in case the constant pool entries should be
   *   moved to the second constant pool
   */
  private void removeField(final BCField afield, final boolean b) {
    final Field[] fds = getBCELClass().getFields();
    int idx = 0;
    final int anidx = afield.getNameIndex();
    for (; idx < fds.length; idx++) {
      final int nidx = fds[idx].getNameIndex();
      if (anidx == nidx) break;
    }
    if (idx < fds.length) { //the normal field exists
      getBCELClass().removeField(fds[idx]);
      if (b) {
        final Field fd = fds[idx];
        updateConstantPoolForFields(afield, fd);
      }
    }
  }

  private void updateConstantPoolForFields(final BCField afield,
                                           final Field fd) {
    final BCConstantPool bcp = getCp();
    final int nidx = bcp.findConstant(fd.getName());
    final ConstantUtf8 cnst = (ConstantUtf8) bcp.getConstant(nidx);
    final int signidx =  fd.getSignatureIndex();
    final int natidx = bcp.findNATConstant(nidx, signidx);
    final ConstantNameAndType natcnst =
      (ConstantNameAndType) bcp.getConstant(natidx);
    bcp.addConstant(cnst, true, bcp.getConstantPool());
    afield.setName(cnst.getBytes());
    natcnst.setNameIndex(afield.getNameIndex() - 1); //we remove one position
    bcp.addConstant(natcnst, true, bcp.getConstantPool());
  }

  /**
   * Updates the fields of the current class with a normal Java field. It
   * looks for a normal field of the same name first and in case of success
   * it updates the field with new information. In case of failure it adds
   * a new {@link Field} to the fields of the current class.
   *
   * @param afield a field to update the class with
   */
  private void updateJavaField(final BCField afield) {
    final Field[] fds = getBCELClass().getFields();
    boolean found = false;
    for (int i = 0; i < fds.length; i++) {
      if (afield.getNameIndex() == fds[i].getNameIndex()) {
        fds[i].setAccessFlags(afield.getAccessFlags());
        int idx = afield.getDescriptorIndex();
        if (getCp().isSecondConstantPoolIndex(idx)) {
          final ConstantUtf8 cnst = (ConstantUtf8)(getCp().getConstant(idx));
          final String val = cnst.getBytes();
          getCp().addConstant(cnst, false, null);
          idx = getCp().findConstant(val);
        }
        fds[i].setSignatureIndex(idx);
        getBMLModifierForField(i).setModifiers(afield.getBMLFlags());
        found = true;
      }
    }
    if (!found) { //TODO this may not work in case the constant pool is modified by hand
      //remove ghost
      getGhostFields().removeBMLField(afield);
      //remove model
      getModelFields().removeBMLField(afield);
      final Field fd = new Field(afield.getAccessFlags(),
                                 afield.getNameIndex(),
                                 afield.getDescriptorIndex(), null,
                                 getBCELClass().getConstantPool().getConstantPool());
      try {
        addField(fd);
      } catch (ReadAttributeException e) {
        logger.warning("Impossible error in reading of a field attribute");
      }
    }
  }

  /**
   * Returns an attribute that is supposed to contain ghost fields and which
   * actually contains no fields.
   *
   * @return the ghost fields attribute with no ghost fields
   */
  protected GhostFieldsAttribute getFreshGhostFields() {
    return new GhostFieldsAttribute(this);
  }

}
