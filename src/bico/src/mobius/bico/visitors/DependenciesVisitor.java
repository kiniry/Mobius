package mobius.bico.visitors;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import mobius.bico.Util;

import org.apache.bcel.util.Repository;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantDouble;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantFloat;
import org.apache.bcel.classfile.ConstantInteger;
import org.apache.bcel.classfile.ConstantInterfaceMethodref;
import org.apache.bcel.classfile.ConstantLong;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.ConstantValue;
import org.apache.bcel.classfile.EmptyVisitor;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.Type;

/**
 * Visits a Java class, and find the dependencies.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class DependenciesVisitor extends EmptyVisitor {


  /** the supposed dependencies found. */
  private final Set<String> fDependencies = new HashSet<String>();
  /** the currently inspected constant pool. */
  private final ConstantPool fCp;
  /** the currently inspected Java class. */
  private final JavaClass fJc;
  
  /**
   * Construct a DeoendenciesVisitor which is associated
   * with a specific class.
   * @param jc the class the visitor is associated with
   */
  private DependenciesVisitor(final JavaClass jc) {
    fCp = jc.getConstantPool();
    fJc = jc;
    
  }

  /** {@inheritDoc} */
  @Override
  public void visitConstantPool(final ConstantPool obj) {
    final Constant[] co = fCp.getConstantPool();
    for (Constant c: co) {
      if (c != null) {
        c.accept(this);
      }
    }
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitConstantClass(final ConstantClass cons) {
    fDependencies.add(cons.getConstantValue(fCp).toString().replace('/', '.'));
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitConstantMethodref(final ConstantMethodref c) {
    final String type = c.getClass(fCp);
    fDependencies.add(type);
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitConstantFieldref(final ConstantFieldref c) {
    final int k = c.getNameAndTypeIndex();
    final ConstantNameAndType nt = (ConstantNameAndType) fCp.getConstant(k);
    String type = nt.getSignature(fCp);
    type = Util.classFormatName2Standard(type);
    if (type != null) {
      fDependencies.add(type);
    }
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitConstantUtf8(final ConstantUtf8 cons) {
    final String type = Util.classFormatName2Standard(cons.getBytes());
    if (type != null) {
      fDependencies.add(type);
    } 
  }

  /**
   * Visits the constant pool the method dependencies, and the field dependencies.
   * @param jc the class inspected
   */
  @Override
  public void visitJavaClass(final JavaClass jc) {
    fCp.accept(this);
    findMethodDependencies();
    findFieldDependencies();
  }
  
  /**
   * Returns all the dependencies found by the visitor.
   * If the dependencies is not found, it is considered as non existing.
   * @param jc the java class to inspect
   * @return all the dependencies, in a String format
   */
  public static Collection<String> getDependencies(final JavaClass jc) {
    final DependenciesVisitor cpVis = new DependenciesVisitor(jc);
    jc.accept(cpVis);
    final Set<String> deps = new HashSet<String>();
    final Repository repos = jc.getRepository();
    for (String str: cpVis.fDependencies) {
      try {
        repos.loadClass(str);
      }
      catch (ClassNotFoundException e) {
        // if one of the class name of the list was part of
        // a fantasy...
        continue;
      }
      deps.add(str);
    }
    return deps;
  }
  
  /** 
   * Find all the dependencies from the methods signatures.
   */
  private void findMethodDependencies() {
    final Method[] ms = fJc.getMethods();
    for (Method met: ms) {
      final Type retType = met.getReturnType();
      if (retType instanceof ReferenceType) {
        final String className = Util.getTypeName((ReferenceType)retType);
        if (className != null) {
          fDependencies.add(className);
        }
      }
    
      final Type[] argT = met.getArgumentTypes();
      if (argT != null) {
        for (Type type: argT) {
          if (type instanceof ReferenceType) {
            final String className = Util.getTypeName((ReferenceType)type);
            if (className != null) {
              fDependencies.add(className);
            }
          }
        }
      }
    
    }
  }
  
  /** 
   * Find all the dependencies from the fields signatures.
   */
  private void findFieldDependencies() {
    final Field[] fs = fJc.getFields();
    for (Field field: fs) {
      final Type type = field.getType();
      if (type instanceof ReferenceType) {
        final String className = Util.getTypeName((ReferenceType) type);
        if (className != null) {
          fDependencies.add(className);
        }
      }
    }
  }

  
  /** {@inheritDoc} */
  @Override
  public void visitConstantDouble(final ConstantDouble obj) {
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitConstantFloat(final ConstantFloat obj) {
  }

  /** {@inheritDoc} */
  @Override
  public void visitConstantInteger(final ConstantInteger obj) {
  }

  /** {@inheritDoc} */
  @Override
  public void visitConstantInterfaceMethodref(final ConstantInterfaceMethodref obj) {
  }

  /** {@inheritDoc} */
  @Override
  public void visitConstantLong(final ConstantLong obj) {
  }

  /** {@inheritDoc} */
  @Override
  public void visitConstantNameAndType(final ConstantNameAndType obj) {
  }


  /** {@inheritDoc} */
  @Override
  public void visitConstantString(final ConstantString obj) {
  }

  /** {@inheritDoc} */
  @Override
  public void visitConstantValue(final ConstantValue obj) {
  }
}
