/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;


import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Utility;

import umbra.instructions.InstructionParser;
import umbra.lib.BMLParsing;
import umbra.lib.BytecodeStrings;
import umbra.lib.UmbraException;
import annot.bcclass.BCClass;
import annot.bcclass.BCConstantPool;
import annot.bcclass.BMLModifiersFlags;
import annot.io.ReadAttributeException;

/**
 * This is a class for lines in bytecode files with a field declaration.
 *
 * TODO: this should be handled by BMLLib
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class FieldLineController extends BytecodeLineController {

  /**
   * Special class used as a result of the method which calculates
   * the access rights of a field in case these are not Java
   * access rights i.e. either the kind of a field (ghost, model) or
   * BML access rights (e.g. spec_public, spec_protected etc.)
   *
   * @author Aleksy Schubert (alx@mimuw.edu.pl)
   * @version a-01
   */
  private static final class ModifException extends Exception {
    int my_modif;
    boolean my_bmlfield;
    public ModifException(int modifier, boolean bmlfield) {
      my_modif = modifier;
      my_bmlfield = bmlfield;
    }
    public int getModif() {
      return my_modif;
    }
    public boolean isBMLField() {
      return my_bmlfield;
    }
  }

  /**
   * The representation of the BML class which takes care of the current
   * field.
   */
  private BCClass my_bcc;
  private String my_type;
  private String my_name;

  private int my_java_modif;
  private int my_bml_modif;
  private int my_field_kind;

  /**
   * This creates an instance of a bytecode line handle to handle
   * a line with a field declaration.
   *
   * @param a_line_text the string representation of the line text
   * @param a_representation the BMLLib representation of the current
   *   class
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public FieldLineController(final String a_line_text,
                             final BMLParsing a_representation) {
    super(a_line_text);
    my_bcc = a_representation.getBcc();
  }


  /**
   * This method checks the correctness of a field declaration line.
   *
   * @return  true if the line is correct
   */
  public boolean correct()  {
    boolean res = true;
    final InstructionParser parser = getParser();
    parser.resetParser();
    int modif = 0;
    int bmodif = 0;
    int field_kind = 0;
    int rmodif = 0;
    while ((rmodif = parser.swallowMnemonic(BytecodeStrings.FIELD_PREFIX)) >=
           0) {
      try {
        modif = setModifier(rmodif, modif, field_kind, bmodif);
      } catch (ModifException e) {
        if (e.isBMLField()) {
          field_kind = modif;
        } else {
          bmodif = e.getModif();
        }
      }
      parser.swallowWhitespace();
    }
    final int typeind = parser.getIndex();
    res = res && parser.swallowArrType();
    final String tmptype = getMy_line_text().substring(typeind,
                                                       parser.getIndex());
    res = res && parser.swallowWhitespace();
    final int fnameind = parser.getIndex();
    res = res && parser.swallowFieldName();
    final String tmpname = getMy_line_text().substring(fnameind,
                                                       parser.getIndex());
    res = res && parser.swallowWhitespace();
    res = res && parser.swallowDelimiter(';');
    if (res) {
      my_type = tmptype;
      my_name = tmpname;
      my_java_modif = modif;
      my_bml_modif = bmodif;
      my_field_kind = field_kind;
    }
    return res;
  }


  /**
   * @param modif
   * @param bmodif
   * @param modif2
   * @param bmodif2
   * @throws ModifException
   */
  private int setModifier(int modif, int modif2, int bmodif, int bmodif2)
    throws ModifException {
    if (modif < BytecodeStrings.BML_FIELD_PREFIX_START) {
      return setJavaModifier(modif, modif2);
    } else if (modif < BytecodeStrings.BML_ACC_PREFIX_START) {
      throw new ModifException(setBMLMField(modif, bmodif), true);
    } else {
      throw new ModifException(setBMLModifier(modif, bmodif), false);
    }
  }


  /**
   * @param modif
   * @param bmodif
   * @return
   */
  private int setBMLMField(int modif, int bmodif) {
    if (bmodif != 0) return 3;
    switch (modif) {
      case 7: //"ghost",
        return 1;
      case 8: //"model"
        return 2;
      default:
        return 3;
    }
  }


  /**
   * @param modif
   * @param bmodif
   */
  private int setBMLModifier(int modif, int bmodif) {
    final int tmp = BMLModifiersFlags.BML_MODIFIERS[modif - 9];
    return bmodif | tmp;
  }


  /**
   * @param modif indeks...
   * @param modif2 current modifiers
   */
  private int setJavaModifier(int modif, int modif2) {
    int tmp = 0;
    switch (modif) {
      case 0: //"public",
        tmp = Constants.ACC_PUBLIC;
        break;
      case 1: //"protected",
        tmp = Constants.ACC_PROTECTED;
        break;
      case 2: //"private",
        tmp = Constants.ACC_PRIVATE;
        break;
      case 3: //"static",
        tmp = Constants.ACC_STATIC;
        break;
      case 4: //"abstract",
        tmp = Constants.ACC_ABSTRACT;
        break;
      case 5: //"final",
        tmp = Constants.ACC_FINAL;
        break;
      case 6: //"strictfp"
        tmp = Constants.ACC_STRICT;
        break;
      default:
        tmp = 0;
    }
    return modif2 | tmp;
  }


  /**
   * This method checks if the particular line can be a field declaration
   * line.
   *
   * @param a_line the string to check if it can be a field declaration line
   * @return <code>true</code> when the string can be a field declaration line,
   *   <code>false</code> otherwise
   */
  public static boolean isFieldLineStart(final String a_line) {
    for (int i = 0; i < BytecodeStrings.FIELD_PREFIX.length; i++) {
      if (a_line.startsWith(BytecodeStrings.FIELD_PREFIX[i])) {
        return true;
      }
    }
    return false;
  }

  /**
   * This method instructs the line controller to remove the field from
   * the class representation. This removes the field without checking
   * the consistency of the class.
   */
  public void removeFromBCEL() {
    //moved to BMLLib
    /*
    if (my_name == null) return;
    final JavaClass jc = my_bcc.getJC();
    final Field[] fds = jc.getFields();
    final Field[] nfds = new Field[fds.length - 1];
    int k = 0;
    for (int i = 0; i < fds.length; i++) {
      final Field f = fds[i];
      nfds[k++] = f;
      if (f.getName().equals(my_name)) {
        k--;
      }
    }
    jc.setFields(nfds);
    */
  }

  /**
   * This method instructs the line controller to add the field to
   * the class representation. This adds the field at the end of
   * the current representation. It also updates the constant pool.
   *
   * @throws UmbraException in case the representation does not allow to
   *   add the content of the line to BML and BCEL representation
   */
  public void addToBCEL() throws UmbraException {
    //moved to BMLLib
    /*
    if (correct()) {
      switch (my_field_kind) {
        case 0: // Java field
          final Field f = getFieldForMe();
          if (f != null) {
            try {
              my_bcc.addField(f);
            } catch (ReadAttributeException e) {
              // TODO This should not happen
              e.printStackTrace();
            }
          }
          break;
        case 1: // Ghost field
          final Field gf = getGhostFieldForMe();
          if (gf != null) {
            my_bcc.addGhostField(gf);
          }
        case 2: // Model field
        default: // Unrecognized field
      }
    }
    */
  }


  /**
   * @return
   * @throws UmbraException
   */
  private Field getGhostFieldForMe() throws UmbraException {
    if (correct()) {
      final BCConstantPool bcp = my_bcc.getCp();
      if (bcp.findConstant(my_name) >= 0) {
        throw new UmbraException();
      }
      bcp.addConstant(new ConstantUtf8(my_name), true, null);
      final int name_index = bcp.findConstant(my_name);
      final Attribute[] attrs = getAttributes();
      final String sname = Utility.getSignature(my_type);
      int signature_index = bcp.findConstant(sname);
      if (signature_index < 0) {
        bcp.addConstant(new ConstantUtf8(sname), true, null);
        signature_index = bcp.findConstant(sname);
      }
      final int pos = bcp.findNATConstant(name_index, signature_index);
      if (pos < 0) {
        bcp.addConstant(new ConstantNameAndType(name_index, signature_index),
                        true, bcp.getCoombinedCP());
      }
      return new Field(my_java_modif, name_index, signature_index,
        attrs, my_bcc.getBCELClass().getConstantPool().getConstantPool());
    }
    return null;
  }


  /**
   * @return
   * @throws UmbraException
   */
  private Field getFieldForMe() throws UmbraException {
    if (correct()) {
      final BCConstantPool bcp = my_bcc.getCp();
      if (bcp.findConstant(my_name) >= 0) {
        throw new UmbraException();
      }
      // TODO: this does not work in case the signatures
      //       happen to exist in the second constant pool, but
      //       do not exist in the first one
      bcp.addConstant(new ConstantUtf8(my_name), false, null);
      final int name_index = bcp.findConstant(my_name);
      final Attribute[] attrs = getAttributes();
      int signature_index =
        bcp.findConstant(Utility.getSignature(my_type));
      if (signature_index < 0) {
        bcp.addConstant(new ConstantUtf8(Utility.getSignature(my_type)),
                        false, null);
        signature_index = bcp.findConstant(Utility.getSignature(my_type));
      }
      final int pos = bcp.findNATConstant(name_index, signature_index);
      if (pos < 0) {
        bcp.addConstant(new ConstantNameAndType(name_index, signature_index),
                        false, bcp.getCoombinedCP());
      }
      return new Field(my_java_modif, name_index, signature_index,
        attrs, my_bcc.getBCELClass().getConstantPool().getConstantPool());
    }
    return null;
  }


  /**
   * @return
   */
  private Attribute[] getAttributes() {
    // TODO Auto-generated method stub
    return new Attribute[0];
  }
}
