package mobius.bmlvcgen.bml.bmllib;

import java.util.Enumeration;

import mobius.bmlvcgen.bml.ClassFile;
import mobius.bmlvcgen.bml.ClassVisitor;
import mobius.bmlvcgen.bml.InvExprVisitor;
import mobius.bmlvcgen.util.Visitable;

import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;

import annot.attributes.clazz.ClassInvariant;
import annot.bcclass.BCClass;
import annot.bcclass.BMLModifiersFlags;

import com.sun.org.apache.xalan.internal.xsltc.compiler.Constants;

/**
 * Bmllib implementation of ClassFile interface.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class BmllibClassFile implements ClassFile {
  // Bmllib handle.
  private final BCClass clazz;
  // BCEL handle.
  private final JavaClass jc;
  // Object used to wrap invariants.
  private final InvExprWrapper invWrapper;
  
  /**
   * Constructor.
   * @param clazz Class to be wrapped.
   */
  public BmllibClassFile(final BCClass clazz) {
    this.clazz = clazz;
    invWrapper = new InvExprWrapper();
    jc = clazz.getJC().getJavaClass();
  }

  /** {@inheritDoc} */
  public void accept(final ClassVisitor v) {
    v.visitVersion(jc.getMajor(), jc.getMinor());
    v.visitFlags(AccessFlag.fromMask(jc.getAccessFlags()));
    v.visitName(jc.getClassName());
    processSuper(v);
    processInterfaces(v);
    processFields(v);
    processMethods(v);
    processInvariants(v);
  }
  
  // Visit superclass name.
  private void processSuper(final ClassVisitor v) {
    try {
      if (jc.getSuperClass() == null) {
        v.visitSuperName(null);
      } else {
        v.visitSuperName(jc.getSuperclassName());
      }
    } catch (final ClassNotFoundException e) {
      v.visitSuperName(null);
    }    
  }
  
  // Visit interfaces.
  private void processInterfaces(final ClassVisitor v) {
    v.beginInterfaces();
    for (final String i : jc.getInterfaceNames()) {
      v.visitInterface(i);
    }
    v.endInterfaces();    
  }

  // Visit fields.
  private void processFields(final ClassVisitor v) {
 // TODO: How to parse field flags??
    v.beginFields();
    for (final Field field : jc.getFields()) {
      v.visitField(new BmllibField(field));
    }
    v.endFields();    
  }
  
  // Visit methods.
  private void processMethods(final ClassVisitor v) {
    v.beginMethods();
    for (int i = 0; i < clazz.getMethodCount(); i++) {
      v.visitMethod(new BmllibMethod(clazz.getMethod(i))); 
    }
    v.endMethods();    
  }
  
  // Wrap all invariants and pass them to a visitor.
  private void processInvariants(final ClassVisitor v) {
    final Enumeration<?> i = clazz.getInvariantEnum();
    while (i.hasMoreElements()) {
      final ClassInvariant inv = (ClassInvariant)i.nextElement();
      final Visitable<InvExprVisitor> wrappedInv = 
        invWrapper.wrap(inv.getInvariant());
      final int flags = inv.getAccessFlags();
      if ((flags & Constants.ACC_STATIC) != 0) {
        throw new UnsupportedOperationException(
          "Static invariants are not supported"
        );
      } else {
        v.visitInvariant(getVisibility(flags), wrappedInv);
      }
    }
  }
  
  // Read visibility from bml flags.
  private static Visibility getVisibility(final int flags) {
    final Visibility result;
    if ((flags & BMLModifiersFlags.BML_SPEC_PUBLIC) != 0) {
      result = Visibility.PUBLIC;
    } else if (
        (flags & BMLModifiersFlags.BML_SPEC_PROTECTED) != 0) {
      result = Visibility.PROTECTED;
    } else {
      result = Visibility.DEFAULT;
    }   
    return result;
  }
}
