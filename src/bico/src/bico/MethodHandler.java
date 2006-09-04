package bico;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;

public class MethodHandler {
	public class MethodNotFoundException extends Exception {
		/** */
		private static final long serialVersionUID = 1L;

		public MethodNotFoundException(MethodType mt) {
			super(mt.toString());
		}
	}
	ArrayList al = new ArrayList();
	private class MethodType {
		public final String name;
		public final Type tret;
		public final Type [] targs;
		public String newName;
		public MethodType(String name, Type[] targs, Type tret) {
			this.targs = targs;
			this.tret = tret; 
			this.name = name;
		}		
		public boolean equals(Object o) {
			if(name == null || tret == null || targs == null)
				return false;
			if(o instanceof MethodType) {
				MethodType mt = (MethodType)o;
				return name.equals(mt.name) &&
						(targs.length == mt.targs.length) &&
							tret.equals(mt.tret);
						
			}
			return false;
		}
		public String toString() {
			return name + " [" + tret + ", " + targs + "]";
		}
	}
	public String getName(InvokeInstruction ii, ConstantPoolGen cpg) throws MethodNotFoundException {
		Type tret = ii.getReturnType(cpg);
		Type [] targs = ii.getArgumentTypes(cpg);
		String name = Executor.coqify(ii.getMethodName(cpg));
		MethodType mt = new MethodType(name, targs, tret);
		MethodType mtold;
		if ((mtold =find(mt)) != null) {
			return mtold.newName;
		}
		else {
			throw new MethodNotFoundException(mt);
		}
	}
	public String getName(MethodGen m) {
		Type [] targs = m.getArgumentTypes();
		Type tret = m.getReturnType();
		String name = Executor.coqify(m.getName());
		MethodType mt = new MethodType(name, targs, tret);
		MethodType mtold;
		if ((mtold =find(mt)) == null) {
			List l = findByName(mt);
			int postfix = l.size();
			if(postfix == 0) {
				mt.newName = mt.name;
			}
			else {
				mt.newName = mt.name + postfix;
			}
			al.add(mt);
			return mt.newName;
		}
		else {
			return mtold.newName;
		}
	}
	
	private List findByName(MethodType mt) {
		Iterator iter = al.iterator();
		ArrayList ret = new ArrayList();
		while(iter.hasNext()) {
			MethodType tmp = (MethodType)iter.next();
			if(tmp.name.equals(mt.name)) {
				ret.add(tmp);
			}
		}
		return ret;
	}
	private MethodType find(MethodType mt) {
		Iterator iter = al.iterator();
		while(iter.hasNext()) {
			MethodType tmp = (MethodType)iter.next();
			if(tmp.equals(mt)) 
				return tmp;
		}
		return null;
	}
	public String getName(Method met) throws MethodNotFoundException {
		Type tret = met.getReturnType();
		Type [] targs = met.getArgumentTypes();
		String name = Executor.coqify(met.getName());
		MethodType mt = new MethodType(name, targs, tret);
		MethodType mtold;
		if ((mtold =find(mt)) != null) {
			return mtold.newName;
		}
		else {
			throw new MethodNotFoundException(mt);
		}
	}
}
