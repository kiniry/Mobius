package b2bpl.bytecode.bml;

import b2bpl.bytecode.BCMethod;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.ast.BMLExpression;
import b2bpl.bytecode.bml.ast.BMLStoreRef;


public interface SpecificationDesugarer {

  BMLExpression getObjectInvariant(JClassType type, boolean includeSupertypes);

  BMLExpression getPrecondition(BCMethod method);

  BMLStoreRef[] getModifiesStoreRefs(BCMethod method);

  BMLExpression getPostcondition(BCMethod method);

  BMLExpression getExceptionalPostcondition(BCMethod method, JType exception);
}
