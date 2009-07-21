package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * TODO describe
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ModifyList extends BCExpression {

  public ModifyList() {
    super(Code.MODIFIES_LIST);
    setSubExprCount(0);
  }

  public ModifyList(final AttributeReader ar) throws ReadAttributeException {
    super(ar, -1);
  }

  public ModifyList(final ModifyExpression[] subExpr) {
    super(Code.MODIFIES_LIST);
    setSubExprCount(subExpr.length);
    for (int i = 0; i  <  subExpr.length; i++) {
      setSubExpr(i, subExpr[i]);
    }
  }

  public void addModify(final ModifyExpression expr) {
    //XXX slow
    final BCExpression[] sub = getAllSubExpr();
    setSubExprCount(sub.length + 1);
    for (int i = 0; i  <  sub.length; i++) {
      setSubExpr(i, sub[i]);
    }
    setSubExpr(sub.length, expr);
  }

  @Override
  protected JavaType checkType1() {
    return JavaBasicType.ModifyExpressionType;
  }

  @Override
  protected int getPriority() {
    return Priorities.LEAF;
  }

  @Override
  public JavaType getType1() {
    return JavaBasicType.ModifyExpressionType;
  }

  public boolean isEmpty() {
    if (getSubExprCount() == 0) {
      return true;
    }
    return false;
    //(getSubExprCount() == 1)
    //  && (getSubExpr(0) == ModifyExpression.Everything);
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    if (getSubExprCount() == 0) {
      return "everything";
    }
    String code = "";
    for (int i = 0; i  <  getSubExprCount(); i++) {
      if (i  >  0) {
        code += ", ";
      }
      final String line = getSubExpr(i).printCode(conf);
      code += line.substring(0, line.length() - 2).substring(2);
    }
    return code;
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    final int size = ar.readItemsCount();
    setSubExprCount(size);
    for (int i = 0; i  <  size; i++) {
      final ModifyExpression me = ar.readModifyExpression();
      setSubExpr(i, me);
    }
  }

  @Override
  public String toString() {
    if (getSubExprCount() == 0) {
      return " << empty list >> ";
    }
    String code = "";
    for (int i = 0; i  <  getSubExprCount(); i++) {
      if (i  >  0) {
        code += ", ";
      }
      code += getSubExpr(i).toString();
    }
    return code;
  }

  @Override
  public void write(final AttributeWriter aw) {
    if (getSubExprCount() == 0) {
      addModify(ModifyExpression.EVERYTHING_MODIF);
    }
    aw.writeAttributeCount(getSubExprCount());
    writeSubExpressions(aw);
  }
}
