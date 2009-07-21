package mobius.bmlvcgen.bml.types;

/**
 * Interface of objects used to visit types.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface TypeVisitor extends 
  PrimitiveTypeVisitor, 
  RefTypeVisitor, 
  ArrayTypeVisitor {
}
