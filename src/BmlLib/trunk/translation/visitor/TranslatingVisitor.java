package visitor;

import java.util.Vector;

import org.apache.bcel.Constants;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

import annot.bcclass.BCClass;
import annot.bcexpression.BCExpression;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.modifies.ModifiesEverything;
import annot.bcexpression.modifies.ModifiesNothing;
import annot.bcexpression.modifies.ModifyList;
import b2bpl.bytecode.BCField;
import b2bpl.bytecode.IConstants;
import b2bpl.bytecode.JArrayType;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.ast.BMLConstraint;
import b2bpl.bytecode.bml.ast.BMLEnsuresClause;
import b2bpl.bytecode.bml.ast.BMLEverythingStoreRef;
import b2bpl.bytecode.bml.ast.BMLExsuresClause;
import b2bpl.bytecode.bml.ast.BMLInvariant;
import b2bpl.bytecode.bml.ast.BMLModifiesClause;
import b2bpl.bytecode.bml.ast.BMLNothingStoreRef;
import b2bpl.bytecode.bml.ast.BMLPredicate;
import b2bpl.bytecode.bml.ast.BMLRequiresClause;
import b2bpl.bytecode.bml.ast.BMLSpecificationCase;
import b2bpl.bytecode.bml.ast.BMLStoreRef;

public class TranslatingVisitor {
  private ConstantPoolGen cpg;

  public JClassType visit(BCClass clazz) {
    cpg = new ConstantPoolGen(clazz.getJC().getConstantPool());
    final JClassType type = new JClassType(clazz.getJC().getClassName());
    b2bpl.bytecode.BCMethod[] resMethods = new b2bpl.bytecode.BCMethod[clazz
        .getMethodCount()];
    for (int i = 0; i < clazz.getMethodCount(); i++) {

      resMethods[i] = visit(clazz.getMethod(i), type);
    }
    type.setDeclarations(new BCField[0], resMethods, new BMLInvariant[0],
                         new BMLConstraint[0]);
    return type;
  }

  public b2bpl.bytecode.BCMethod visit(annot.bcclass.BCMethod method,
                                       JClassType owner) {
    MethodGen bcm = method.getBcelMethod();
    JType returnType = visit(bcm.getReturnType());
    int len = bcm.getArgumentTypes().length;
    JType[] paramTypes = new JType[len];
    for (int i = 0; i < len; i++) {
      paramTypes[i] = visit(bcm.getArgumentType(i));
    }
    int excLen = bcm.getExceptions().length;
    JClassType[] exc = new JClassType[excLen];
    for (int i = 0; i < excLen; i++) {
      exc[i] = new JClassType(bcm.getExceptions()[i]);
    }
    int flags = translateFlags(bcm.getAccessFlags());
    b2bpl.bytecode.BCMethod resMethod = new b2bpl.bytecode.BCMethod(
                                                                    flags,
                                                                    owner,
                                                                    bcm
                                                                        .getName(),
                                                                    returnType,
                                                                    paramTypes,
                                                                    exc);
    InstructionList instructions = bcm.getInstructionList();
    final b2bpl.bytecode.Instructions retInstr = new b2bpl.bytecode.Instructions();
    if (instructions != null) {
      final org.apache.bcel.generic.InstructionHandle[] origInstr = instructions
          .getInstructionHandles();
      for (int i = 0; i < origInstr.length; i++) {

        retInstr.add(visit(origInstr[i].getInstruction()));
      }
    }
    resMethod.setSpecification(visit(method.getMspec()));

    System.out.println("specyfikacje to " + visit(method.getMspec()));
    System.out.println("A ca³a metoda to " + resMethod);
    return resMethod;
  }


  private int translateFlags(int flags) {
    if ((flags & Constants.ACC_PUBLIC) != 0)
      return IConstants.ACC_PUBLIC;
    if ((flags & Constants.ACC_PROTECTED) != 0)
      return IConstants.ACC_PROTECTED;
    return IConstants.ACC_PRIVATE;

  }

  public b2bpl.bytecode.bml.ast.BMLMethodSpecification visit(
                                                             annot.attributes.MethodSpecification spec) {
    if (spec == null)
      return null;
    Vector<annot.attributes.SpecificationCase> cases = spec
        .getSpecificationCases();
    Vector<BMLSpecificationCase> translatedCases = new Vector<BMLSpecificationCase>();
    for (annot.attributes.SpecificationCase specCase : cases) {
      ExpressionRoot<AbstractFormula> prec = specCase.getPrecondition();
      ExpressionRoot<AbstractFormula> post = specCase.getPostcondition();
      ExpressionRoot<ModifyList> modifies = specCase.getModifies();
      translatedCases
          .add(new BMLSpecificationCase(new BMLRequiresClause(visit(prec)),
                                        visit(modifies),
                                        new BMLEnsuresClause(visit(post)),
                                        BMLExsuresClause.EMPTY_ARRAY));

    }
    return new b2bpl.bytecode.bml.ast.BMLMethodSpecification(
                                                             new BMLRequiresClause(
                                                                                   new BMLPredicate(
                                                                                                    b2bpl.bytecode.bml.ast.BMLBooleanLiteral.TRUE)),
                                                             translatedCases
                                                                 .toArray(new BMLSpecificationCase[1]));
  }

  public BMLModifiesClause visit(ExpressionRoot<ModifyList> modifies) {
    ModifyList list = modifies.getExpression();
    BCExpression[] expr = list.getAllSubExpr();
    if (expr.length != 1)
      return new BMLModifiesClause(BMLStoreRef.EMPTY_ARRAY);
    if (expr[0] instanceof ModifiesEverything)
      return new BMLModifiesClause(BMLEverythingStoreRef.EVERYTHING);
    if (expr[0] instanceof ModifiesNothing)
      return new BMLModifiesClause(BMLNothingStoreRef.NOTHING);
    return new BMLModifiesClause(BMLStoreRef.EMPTY_ARRAY);
  }

  public b2bpl.bytecode.bml.ast.BMLPredicate visit(
                                                   ExpressionRoot<AbstractFormula> rootFormula) {
    ExpressionTranslator translator = new ExpressionTranslator();
    return new b2bpl.bytecode.bml.ast.BMLPredicate(translator.visit(rootFormula
        .getExpression()));
  }

  public b2bpl.bytecode.InstructionHandle visit(
                                                final org.apache.bcel.generic.Instruction instruction) {
    final b2bpl.bytecode.InstructionHandle res = new b2bpl.bytecode.InstructionHandle();
    InstructionTranslator translator = new InstructionTranslator(cpg, this);
    res.setInstruction(translator.translate(instruction));

    return res;
  }

  public JArrayType visit(ArrayType type) {
    return new JArrayType(visit(type.getElementType()), type.getDimensions());
  }

  public JType visit(Type type) {
    return JType.fromDescriptor(type.getSignature());
  }

  public JReferenceType visit(ObjectType type) {
    return null;
  }
}
