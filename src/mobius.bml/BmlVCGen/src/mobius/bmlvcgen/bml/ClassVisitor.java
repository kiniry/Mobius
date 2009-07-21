package mobius.bmlvcgen.bml;

import java.util.EnumSet;

import mobius.bmlvcgen.bml.ClassFile.AccessFlag;
import mobius.bmlvcgen.bml.ClassFile.Visibility;
import mobius.bmlvcgen.util.Visitable;

/**
 * Interface of class file visitors.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface ClassVisitor {
  /**
   * Visit class file version.
   * @param major Major version.
   * @param minor Minor version.
   */
  void visitVersion(int major, int minor);
  
  /**
   * Visit class access flags.
   * @param flags Flags.
   */
  void visitFlags(EnumSet<AccessFlag> flags);
  
  /**
   * Visit fully qualified name of this class.
   * @param name FQN of this class.
   */
  void visitName(String name);
  
  /**
   * Visit superclass name.
   * @param name FQN of superclass 
   * (null if processing Object class).
   */
  void visitSuperName(String name);
  
  /**
   * Called before visiting interfaces.
   */
  void beginInterfaces();
  
  /**
   * Visit implemented interface.
   * @param name Interface name.
   */
  void visitInterface(String name);
  
  /**
   * Called after visiting interfaces.
   */
  void endInterfaces();
  
  /**
   * Called before visiting invariants.
   */
  void beginInvariants();
  
  /**
   * Visit an invariant.
   * @param visibility Invariant visibility modifier.
   * @param inv Invariant expression.
   */
  void visitInvariant(Visibility visibility, 
                      Visitable<? super InvExprVisitor> inv);
  
  /**
   * Called after visiting invariants.
   */
  void endInvariants();
  
  /**
   * Called before visiting field declarations.
   */
  void beginFields();

  /**
   * Visit a field declaration.
   * @param field Field declaration.
   */
  void visitField(Field field);
  
  /**
   * Called after visiting field declarations.
   */
  void endFields();
  
  /**
   * Called before visiting method declarations.
   */
  void beginMethods();

  /**
   * Visit a method declaration.
   * @param method Method declaration.
   */
  void visitMethod(Method method);
  
  /**
   * Called after visiting method declarations.
   */
  void endMethods();
}
