package mobius.directVCGen.formula.jmlTranslator;

import mobius.directVCGen.formula.*;

import java.util.Properties;
import escjava.ast.ResExpr;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.Term;
import javafe.ast.BinaryExpr;
import javafe.ast.LiteralExpr;
import javafe.ast.VariableAccess;

public class JmlExprToFormula {

	JmlVisitor v;
	
	public JmlExprToFormula(JmlVisitor visitor) {
		v = visitor;
	}

	public Term and(BinaryExpr expr, Object o) {
		Object pred = ((Properties) o).get("pred");		
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
				
		if (pred.equals(false) && (t1.getSort() != Logic.sort)&&(t2.getSort() != Logic.sort))
			return Bool.and(t1, t2);
		else
			return Logic.and(Logic.boolToProp(t1),Logic.boolToProp(t2));			
	}
	
	
	public Object or(BinaryExpr expr, Object o) {
		Object pred = ((Properties) o).get("pred");		
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
				
		if (pred.equals(false) && (t1.getSort() != Logic.sort)&&(t2.getSort() != Logic.sort))
			return Bool.or(t1, t2);
		else
			return Logic.or(Logic.boolToProp(t1),Logic.boolToProp(t2));			
	}
	
	
	public Term add(BinaryExpr expr, Object o) {
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
		
		if (t1.getSort() != Num.sortInt) {
			return Ref.add(t1,t2);
		}
		else
		{
			return Num.add(t1,t2);
		}
	}
	
	/**
	 * Returns either a sortPred or sortBool equality term depending of the expection of the upper method
	 * @param expr
	 * @param o the Properties object, contains information about the excepted sort of the return value
	 * @return term in the excepted sort, if possible
	 */
	public Object eq(BinaryExpr expr, Object o) {
		Object pred = ((Properties) o).get("pred");
		//set Properties.prop:=false (equality operation wants sortBool)
		Object prop = ((Properties) o).put("pred", false);
		Term t1 = (Term)expr.left.accept(v,prop);
		Term t2 = (Term)expr.right.accept(v,prop);
		
		if (prop.equals(false) && (t1.getSort() != Logic.sort)&&(t2.getSort() != Logic.sort))
				return Bool.equals(t1, t2);	
		else if (pred.equals(true) && (t1.getSort() != Logic.sort)&& (t2.getSort() != Logic.sort))
				return Logic.equals(t1,t2);		
		else
			return Logic.fullImplies(Logic.boolToProp(t1),Logic.boolToProp(t2));	
	}

	
	/**
	 * ne(t1,t2) <--> not(equal(t1,t2))
	 */
	public Object ne(BinaryExpr expr, Object o) {
		Object pred = ((Properties) o).get("pred");		
		Term t = (Term) eq(expr,o);
				
		if (pred.equals(false) && (t.getSort() != Logic.sort))
			return Bool.not(t);
		else
			return Logic.not(Logic.boolToProp(t));	
	}

	
	
	public Object ge(BinaryExpr expr, Object o) {
		Object pred = ((Properties) o).get("pred");		
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
				
		if (pred.equals(false) && (t1.getSort() != Logic.sort)&&(t2.getSort() != Logic.sort))
			return Bool.ge(t1, t2);
		else
			return Logic.ge(Logic.boolToProp(t1),Logic.boolToProp(t2));			
	}

	
	public Object gt(BinaryExpr expr, Object o) {
		Object pred = ((Properties) o).get("pred");		
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
				
		if (pred.equals(false) && (t1.getSort() != Logic.sort)&&(t2.getSort() != Logic.sort))
			return Bool.gt(t1, t2);
		else
			return Logic.gt(Logic.boolToProp(t1),Logic.boolToProp(t2));			
	}
	
	
	public Object le(BinaryExpr expr, Object o) {
		Object pred = ((Properties) o).get("pred");		
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
				
		if (pred.equals(false) && (t1.getSort() != Logic.sort)&&(t2.getSort() != Logic.sort))
			return Bool.le(t1, t2);
		else
			return Logic.le(Logic.boolToProp(t1),Logic.boolToProp(t2));			
	}

	
	public Object lt(BinaryExpr expr, Object o) {
		Object pred = ((Properties) o).get("pred");		
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
				
		if (pred.equals(false) && (t1.getSort() != Logic.sort)&&(t2.getSort() != Logic.sort))
			return Bool.lt(t1, t2);
		else
			return Logic.lt(Logic.boolToProp(t1),Logic.boolToProp(t2));			
	}

	public Object bitor(BinaryExpr expr, Object o) {
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
		return Expression.bitor(t1, t2);
	}

	public Object bitxor(BinaryExpr expr, Object o) {
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
		return Expression.bitxor(t1, t2);
	}

	public Object bitand(BinaryExpr expr, Object o) {
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
		return Expression.bitand(t1, t2);
	}

	public Object lshift(BinaryExpr expr, Object o) {
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
		return Num.lshift(t1, t2);
	}

	public Object rshift(BinaryExpr expr, Object o) {
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
		return Num.rshift(t1, t2);
	}

	public Object urshift(BinaryExpr expr, Object o) {
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
		return Num.urshift(t1, t2);
	}

	public Object sub(BinaryExpr expr, Object o) {
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
		return Num.sub(t1, t2);
	}

	public Object div(BinaryExpr expr, Object o) {
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
		return Num.div(t1, t2);
	}

	public Object mod(BinaryExpr expr, Object o) {
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
		return Num.mod(t1, t2);
	}

	public Object star(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object assign(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgmul(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgdiv(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgrem(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgadd(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgsub(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asglshift(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgrshift(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgurshif(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgbitand(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object implies(BinaryExpr expr, Object o) {
		Object pred = ((Properties) o).get("pred");		
		Term t1 = (Term)expr.left.accept(v,o);
		Term t2 = (Term)expr.right.accept(v,o);
				
		if (pred.equals(false) && (t1.getSort() != Logic.sort)&&(t2.getSort() != Logic.sort))
			return Bool.implies(t1, t2);
		else
			return Logic.implies(Logic.boolToProp(t1),Logic.boolToProp(t2));			
	}

	
	public Object explies(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}


	public Object iff(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object niff(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object subtype(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object dotdot(BinaryExpr expr, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	
	

	
	/* To know how a tag and the type of an expression fits together look at the list given in LiteralExpr -> isValidValue(int tag, Object value)
	
	 if (tag == TagConstants.NULLLIT)    return value == null;
         if (tag == TagConstants.BOOLEANLIT) return value instanceof Boolean;
         if (tag == TagConstants.BYTELIT)    return value instanceof Byte;
         if (tag == TagConstants.SHORTLIT)   return value instanceof Short;
         if (tag == TagConstants.CHARLIT)    return value instanceof Integer;
         if (tag == TagConstants.INTLIT)     return value instanceof Integer;
         if (tag == TagConstants.LONGLIT)    return value instanceof Long;
         if (tag == TagConstants.FLOATLIT)   return value instanceof Float;
         if (tag == TagConstants.DOUBLELIT)  return value instanceof Double;
         if (tag == TagConstants.STRINGLIT)  return value instanceof String;
	 */
	public Object lit(LiteralExpr x, Object o) {
		switch (x.getTag())
		{
		case TagConstants.BOOLEANLIT: 
			return Bool.value((Boolean) x.value);
		case TagConstants.INTLIT:
			return Num.value((Integer) x.value);
		case TagConstants.LONGLIT:
			return Num.value((Long) x.value);
		case TagConstants.CHARLIT:
			return Num.value((Character) x.value);
		case TagConstants.FLOATLIT:
			return Num.value((Float) x.value);
		case TagConstants.DOUBLELIT:
			return Num.value((Double) x.value);
		case TagConstants.STRINGLIT:
			break;
		case TagConstants.NULLLIT:
			break;
		case TagConstants.BYTELIT:
			return Num.value((Byte) x.value);
		case TagConstants.SHORTLIT:
			return Num.value((Short) x.value);
			
		default: 
			throw new IllegalArgumentException("LiteralExpr " + x.toString() + " has unknown type.");  //should be unreachable
		}
		return null;
	}

	//Claudia: Not yet implemented
	public Object res(ResExpr x, Object o) {
		x.getTag(); //wrong tag
		
		return Num.value(3); //Testing
	}

	public Object varAccess(VariableAccess x, Object o) {	
		return Ref.strValue(x.toString());
	}
	

}
