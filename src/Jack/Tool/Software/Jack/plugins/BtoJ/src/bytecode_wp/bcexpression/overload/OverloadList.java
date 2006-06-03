/*
 * Created on May 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcexpression.overload;

import jack.util.Logger;

import java.util.Vector;

import bytecode_wp.bcexpression.ArrayAccessExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class OverloadList {
	/*
	 * private Tree left; private Tree right;
	 */

	private Vector overloads;

	public OverloadList(Expression expr1, Expression expr2) {
		OverloadEqUnit unit = new OverloadEqUnit(expr1, expr2);
		overloads = new Vector();
		overloads.add(unit);
		/* setLeft(left); */
	}

	public OverloadList() {

	}

	public OverloadList(Vector _overloads) {
		overloads = _overloads;
	}

	public void overload(OverloadUnit unit) {
		if (overloads == null) {
			overloads = new Vector();
		}
		overloads.add(unit);
	}

	/**
	 * find the update which updates for <b>expr</b> if there is such an update
	 * the update is returned, otherwise return null
	 * 
	 * @param expr
	 * @return
	 */
	protected OverloadUnit getExpressionOverloading(Expression expr) {
		if (overloads == null) {
			return null;
		}
		for (int i = 0; i < overloads.size(); i++) {
			OverloadUnit unit = (OverloadUnit) (overloads.get(i));
			OverloadUnit overloading = unit.getExpressionOverloading(expr);
			if (overloading != null) {
				return overloading;
			}
		}
		return null;
	}

	/*	*//**
			 * deprecated
			 * 
			 * @param left
			 * @param right
			 */
	/*
	 * public OverloadList(Overload left, Overload right) { setLeft(left);
	 * setRight(right); }
	 */

	public OverloadList substitute(Expression e1, Expression e2) {
		if (overloads == null) {
			return this;
		}

		for (int i = 0; i < overloads.size(); i++) {
			OverloadUnit unit = (OverloadUnit) (overloads.get(i));
			unit = (OverloadUnit) unit.substitute(e1, e2);
			overloads.set(i, unit);
		}
		return this;
	}

	/**
	 * @param tree
	 */
	/*
	 * public void setLeft(Tree tree) { left = tree; }
	 */

	/**
	 * @param tree
	 */
	/*
	 * public void setRight(Tree tree) { right = tree; }
	 */

	public String toString() {
		String s = "";

		for (int i = 0; i < overloads.size(); i++) {
			OverloadUnit unit = (OverloadUnit) (overloads.get(i));
			s = s + " " + unit.toString();
		}
		return s;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.substitution.Tree#copy()
	 */
	public OverloadList copy() {
		if (overloads == null) {
			Logger.err.println("Warning : a null list of overloads ");
			return null;
		}
		OverloadList overLoadCopy = new OverloadList();
		for (int i = 0; i < overloads.size(); i++) {
			OverloadUnit unit = (OverloadUnit) (overloads.get(i));
			unit = (OverloadUnit) unit.copy();
			overLoadCopy.overload(unit);
		}
		return overLoadCopy;
	}

	public Vector getOverloads() {
		return overloads;
	}

	public boolean equals(Object obj) {
		if (!(obj instanceof OverloadList)) {
			return false;
		}
		OverloadList list = (OverloadList) obj;
		if (getNumberOverload() != list.getNumberOverload()) {
			return false;
		}
		for (int i = 0; i < getNumberOverload(); i++) {
			OverloadUnit u1 = (OverloadUnit) overloads.elementAt(i);
			OverloadUnit u2 = (OverloadUnit) list.getOverloads().elementAt(i);
			if (!u1.equals(u2)) {
				return false;
			}
		}
		return true;

	}
	


	public int getNumberOverload() {
		if (overloads == null) {
			return 0;
		}
		return overloads.size();
	}

	public OverloadList atState(int instrIndex, Expression expr) {
		if (overloads == null) {
			return this;
		}
		for (int i = 0; i < overloads.size(); i++) {
			OverloadUnit unit = (OverloadUnit) (overloads.get(i));
			unit = (OverloadUnit) unit.atState(instrIndex, expr);
			overloads.set(i, unit);
		}
		return this;

	}
	
	public OverloadList atState(int instrIndex) {
		if (overloads == null) {
			return this;
		}
		for (int i = 0; i < overloads.size(); i++) {
			OverloadUnit unit = (OverloadUnit) (overloads.get(i));
			unit = (OverloadUnit) unit.atState(instrIndex);
			overloads.set(i, unit);
		}
		return this;

	}

	public void simplifyFieldUpdate() {
		if (overloads == null) {
			return;
		}
		for ( int i = 0; i < overloads.size(); i++ ) {
			Expression obj = ( (OverloadUnit)overloads.get(i)).getObject();
			for (int from = i + 1; from < overloads.size(); from++) {
				OverloadUnit u = (OverloadUnit) (overloads.get(from));
				OverloadUnit overloading = u.getExpressionOverloading(obj);
				if (overloading != null) {
					overloads.remove(from);
				}

			}
		}
	}

	public void simplifyArrUpdate() {

		if (overloads == null) {
			return;
		}
		for (int i = 0; i < overloads.size(); i++) {
			OverloadUnit unit = (OverloadUnit) overloads.get(i);

			Expression updating = unit.getObject();
			// if there are updates for the same variable added after the update
			// unit
			// then remove them (this means that the same expression has been
			// assigned twice)
			// for instance
			// a[1] =2;
			// a[1] = 3; keep only the last assignment
			ArrayAccessExpression arrAcc = null;
			if (updating instanceof ArrayAccessExpression) {
				arrAcc = (ArrayAccessExpression) updating;
			}

			if (updating instanceof FunctionOverload) {
				RefFunction fApp = ((FunctionOverload) updating)
						.getFunction();
				OverloadList list = ((FunctionOverload) updating).getMap();
				list.simplifyArrUpdate();
				if (fApp instanceof ArrayAccessExpression) {
					arrAcc = (ArrayAccessExpression) fApp;
					list.removeUpdate(arrAcc);
				}
				updating = ((FunctionOverload) updating).simplify();
				unit.setObject(updating);

			}

			for (int from = i + 1; from < overloads.size(); from++) {
				OverloadUnit u = (OverloadUnit) (overloads.get(from));
				OverloadUnit overloading = u.getExpressionOverloading(arrAcc);
				if (overloading != null) {
					overloads.remove(from);
				}

			}

			/*
			 * if (old != unit) { overloads.remove( i); overloads.add( i, unit); }
			 */

		}

	}

	private void removeUpdate(Expression e) {
		for (int i = 0; i < overloads.size(); i++) {
			OverloadUnit u = (OverloadUnit) (overloads.get(i));
			OverloadUnit overloading = u.getExpressionOverloading(e);
			if (overloading != null) {
				overloads.remove(i);
			}
		}

	}
}
