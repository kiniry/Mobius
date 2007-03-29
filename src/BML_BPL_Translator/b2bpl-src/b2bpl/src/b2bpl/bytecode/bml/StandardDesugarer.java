package b2bpl.bytecode.bml;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;

import b2bpl.bytecode.BCMethod;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.ast.BMLBinaryLogicalExpression;
import b2bpl.bytecode.bml.ast.BMLBooleanLiteral;
import b2bpl.bytecode.bml.ast.BMLExpression;
import b2bpl.bytecode.bml.ast.BMLExsuresClause;
import b2bpl.bytecode.bml.ast.BMLInvariant;
import b2bpl.bytecode.bml.ast.BMLMethodSpecification;
import b2bpl.bytecode.bml.ast.BMLOldExpression;
import b2bpl.bytecode.bml.ast.BMLSpecificationCase;
import b2bpl.bytecode.bml.ast.BMLStoreRef;


public class StandardDesugarer implements SpecificationDesugarer {

  public BMLExpression getObjectInvariant(
      JClassType type,
      boolean includeSupertypes) {
    List<BMLExpression> accumInvariants = new ArrayList<BMLExpression>();
    accumObjectInvariants(type, includeSupertypes, accumInvariants);
    return join(BMLBinaryLogicalExpression.Operator.AND, accumInvariants);
  }

  public void accumObjectInvariants(
      JClassType type,
      boolean includeSupertypes,
      List<BMLExpression> accumInvariants) {
    for (BMLInvariant invariant : type.getInvariants()) {
      if (!invariant.isStatic()) {
        accumInvariants.add(invariant.getPredicate());
      }
    }

    if (includeSupertypes) {
      JClassType supertype = type.getSupertype();
      if (supertype != null) {
        accumObjectInvariants(supertype, includeSupertypes, accumInvariants);
      }
      for (JClassType iface : type.getInterfaces()) {
        accumObjectInvariants(iface, includeSupertypes, accumInvariants);
      }
    }
  }

  public BMLExpression getPrecondition(BCMethod method) {
    List<BCMethod> overrides = method.getOverrides();
    List<BMLExpression> accumPreconditions = new ArrayList<BMLExpression>();
    for (BCMethod override : overrides) {
      BMLMethodSpecification spec = override.getSpecification();
      if (spec != null) {
        // REVIEW[om]: This is a temporary hack to cope with what JACK gives us
        //             when we have a single specification case.
        if (spec.getCases().length == 1) {
          accumPreconditions.add(spec.getRequires().getPredicate());
        } else {
          for (BMLSpecificationCase specCase : spec.getCases()) {
            accumPreconditions.add(specCase.getRequires().getPredicate());
          }
        }
      }
    }
    return join(BMLBinaryLogicalExpression.Operator.OR, accumPreconditions);
  }

  public BMLStoreRef[] getModifiesStoreRefs(BCMethod method) {
    List<BCMethod> overrides = method.getOverrides();
    HashSet<BMLStoreRef> accumStoreRefs = new LinkedHashSet<BMLStoreRef>();
    for (BCMethod override : overrides) {
      BMLMethodSpecification spec = override.getSpecification();
      if (spec != null) {
        for (BMLSpecificationCase specCase : spec.getCases()) {
          for (BMLStoreRef storeRef : specCase.getModifies().getStoreRefs()) {
            accumStoreRefs.add(storeRef);
          }
        }
      }
    }
    return accumStoreRefs.toArray(new BMLStoreRef[accumStoreRefs.size()]);
  }

  public BMLExpression getPostcondition(BCMethod method) {
    List<BCMethod> overrides = method.getOverrides();
    List<BMLExpression> accumPostconditions = new ArrayList<BMLExpression>();
    for (BCMethod override : overrides) {
      BMLMethodSpecification spec = override.getSpecification();
      if (spec != null) {
        // REVIEW[om]: This is a temporary hack to cope with what JACK gives us
        //             when we have a single specification case.
        if (spec.getCases().length == 1) {
          accumPostconditions.add(new BMLBinaryLogicalExpression(
              BMLBinaryLogicalExpression.Operator.IMPLIES,
              new BMLOldExpression(spec.getRequires().getPredicate()),
              spec.getCases()[0].getEnsures().getPredicate()));
        } else {
          for (BMLSpecificationCase specCase : spec.getCases()) {
            accumPostconditions.add(new BMLBinaryLogicalExpression(
                BMLBinaryLogicalExpression.Operator.IMPLIES,
                new BMLOldExpression(specCase.getRequires().getPredicate()),
                specCase.getEnsures().getPredicate()));
          }
        }
      }
    }
    return join(BMLBinaryLogicalExpression.Operator.AND, accumPostconditions);
  }

  public BMLExpression getExceptionalPostcondition(
      BCMethod method,
      JType exception) {
    List<BCMethod> overrides = method.getOverrides();
    List<BMLExpression> accumPostconditions = new ArrayList<BMLExpression>();
    for (BCMethod override : overrides) {
      BMLMethodSpecification spec = override.getSpecification();
      if (spec != null) {
        // REVIEW[om]: This is a temporary hack to cope with what JACK gives us
        //             when we have a single specification case.
        if (spec.getCases().length == 1) {
          accumPostconditions.add(new BMLBinaryLogicalExpression(
              BMLBinaryLogicalExpression.Operator.IMPLIES,
              new BMLOldExpression(spec.getRequires().getPredicate()),
              getXPostcondition(exception, spec.getCases()[0].getExsures())));
        } else {
          for (BMLSpecificationCase specCase : spec.getCases()) {
            accumPostconditions.add(new BMLBinaryLogicalExpression(
                BMLBinaryLogicalExpression.Operator.IMPLIES,
                new BMLOldExpression(specCase.getRequires().getPredicate()),
                getXPostcondition(exception, specCase.getExsures())));
          }
        }
      }
    }
    return join(BMLBinaryLogicalExpression.Operator.AND, accumPostconditions);
  }

  private static BMLExpression getXPostcondition(
      JType exception,
      BMLExsuresClause[] exsures) {
    List<BMLExpression> accumPostconditions = new ArrayList<BMLExpression>();
    for (BMLExsuresClause exsure : exsures) {
      if (exsure.getExceptionType().equals(exception)) {
        accumPostconditions.add(exsure.getPredicate());
      }
    }
    return join(BMLBinaryLogicalExpression.Operator.AND, accumPostconditions);
  }

  private static BMLExpression join(
      BMLBinaryLogicalExpression.Operator joinOperator,
      List<BMLExpression> expressions) {
    if (expressions.size() > 0) {
      BMLExpression invariant = expressions.get(0);
      for (int i = 1; i < expressions.size(); i++) {
        invariant = new BMLBinaryLogicalExpression(
            joinOperator,
            invariant,
            expressions.get(i));
      }
      return invariant;
    }
    return BMLBooleanLiteral.TRUE;
  }
}
