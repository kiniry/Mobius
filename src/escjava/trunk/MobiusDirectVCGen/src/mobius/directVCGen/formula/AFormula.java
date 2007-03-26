package mobius.directVCGen.formula;

import java.util.Iterator;
import java.util.Vector;

import mobius.directVCGen.formula.expression.Variable;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;
import mobius.directVCGen.formula.type.TypeErrorException;


public abstract class AFormula implements IFormula {
	private final Type fType;
	private final Vector<IFormula> fArgs;

	//@ requires (type != null); 
	public AFormula(Type type) {
		this(type, new Vector<IFormula>());
	}
	
	//@ requires (type != null) && (args != null); 
	public AFormula(Type type, Vector<IFormula> args) {
		fType = type;
		fArgs = args;
	}

	public IFormula get(int index) {
		return fArgs.get(index);
	}
	
	public void set(int slot, IFormula f) {
		fArgs.set(slot, f);
	}
	
	public void add(IFormula form) {
		fArgs.add(form);
	}
	
	
	/**
	 * Return the type of the formula fully applied to its arguments.
	 * @return 
	 */
	public Type getType () {
		return fType;
	}


	public Iterator<IFormula> iterator() {
		return fArgs.iterator();
	}
	
	
	public IFormula subst(Variable v, IFormula e) {
    	Vector<IFormula> args = new Vector<IFormula>();
    	Iterator<IFormula> iter = fArgs.iterator();
    	boolean bHasChanged = false;
    	while(iter.hasNext()) {
    		IFormula f = iter.next();
    		IFormula newF = f.subst(v, e);
    		if(f != newF) {
    			bHasChanged = true;
    		}
    		args.add(newF);
    	}
		if (bHasChanged) {
			return clone(args);
		}
		return this;
	}

	/**
	 * Cloning the object by replacing the arguments by the given ones.
	 * @param args the arguments to replace the previous one with
	 * @return a new 'cloned' object (the default implementation return this)
	 */
	public abstract IFormula clone(Vector<IFormula> args);
	
	
	public void checkType(FunType type) throws TypeErrorException {
		if(type.size() - 1 != fArgs.size()) {
			throw new TypeErrorException("Not the right number of args!");
		}
		Iterator<IFormula> iterArgs = fArgs.iterator();
		Iterator<IFormula> iterType = type.iterator();
		while(iterArgs.hasNext()) {
			IFormula arg = iterArgs.next();
			IFormula typ = iterType.next();
			if(!arg.getType().equals(typ))
				throw new TypeErrorException(arg.getType()+ 
						" is not the same as " + typ.getType());
		}
		IFormula t;
		if((t = iterType.next()) != getType()) {
			throw new TypeErrorException("The return type is " + getType() + " instead of " + t);
		}
	}

}
