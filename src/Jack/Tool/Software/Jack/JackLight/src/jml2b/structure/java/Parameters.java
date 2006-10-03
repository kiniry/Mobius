//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Parameters.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/*******************************************************************************/
package jml2b.structure.java;

import java.io.Serializable;
import java.util.Enumeration;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.ParseException;
import jml2b.link.LinkContext;
import jml2b.link.LinkUtils;
import jml2b.link.Linkable;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.IAParameters;
import antlr.collections.AST;

/**
 * @author A. Requet L. Burdy
 */
public class Parameters extends IAParameters implements Linkable, Serializable {
	/** vector containing fields corresponding to the signature
	 */
	public Vector signature;

	/*@
	  @ invariant signature != null;
	  @*/

	public Parameters() {
		signature = new Vector();
	}

	public Parameters(IJml2bConfiguration config, String methodDescriptor) {
		String parameterDescriptor =
			methodDescriptor.substring(1, methodDescriptor.indexOf(")"));
		signature = new Vector();
		while (parameterDescriptor.length() > 0) {
			signature.add(
				new Field(new ParsedItem(), new Type(config, parameterDescriptor), ""));
			int i = 0;
			loop : while (true) {
				switch (parameterDescriptor.charAt(i)) {
					case 'F' :
					case 'D' : 
						throw new InternalError("Parameters(String) Type not handle: " + parameterDescriptor);
					case 'B' :
					case 'C' :
					case 'I' :
					case 'S' :
					case 'Z' :
						parameterDescriptor = parameterDescriptor.substring(1+i);
						break loop;
					case 'L' :
						parameterDescriptor =
							parameterDescriptor.substring(
								parameterDescriptor.indexOf(';')+1);
						break loop;
					case '[' :
						i++;
				}
			}
		}
	}

	/*@
	  @ requires ast != null;
	  @ requires \typeof(ast) <: \type(LineAST);
	  @*/
	public AST parse(JmlFile jmlFile, AST ast) throws Jml2bException {
		switch (ast.getType()) {
			case JmlDeclParserTokenTypes.COMMA :
				{
					AST tmp = ast.getFirstChild();
					parse(jmlFile, tmp);
					parse(jmlFile, tmp.getNextSibling());
					return ast.getNextSibling();
				}
			case JmlDeclParserTokenTypes.PARAM :
				{
					AST tmp = ast.getFirstChild();
					String param_name;

					// ignore final modifiers in signatures
					if (tmp.getType()
						== JmlDeclParserTokenTypes.LITERAL_final) {
						tmp = tmp.getNextSibling();
					}
					Type type = new Type(jmlFile, tmp);
					tmp = type.parse(tmp);

					if (tmp.getType() != JmlDeclParserTokenTypes.IDENT) {
						throw new ParseException(
							jmlFile,
							(LineAST) ast,
							"Parameters: unexpected token: "
								+ "expected IDENT, got "
								+ tmp.getType());
					}
					//                    Box b = new Box();
					//                    b.setX(tmp);
					//                    b.setJmlFile(jmlFile);
					param_name = tmp.getText();
					//                    b.setY(param_name.length());
					// check for a DIMS node after the name
					tmp = tmp.getNextSibling();
					if (tmp != null
						&& tmp.getType() == JmlDeclParserTokenTypes.DIMS) {
						type = Type.addDims(jmlFile, tmp, type);
					}

					// create a new Field corresponding to the parameter (name and
					// type), and add it to the parameter list
					Field param = new Field(new ParsedItem(), type, param_name);
					signature.add(param);
					return ast.getNextSibling();
				}
			default :
				// no parameters, leave signature unchanged
				return ast;
		}
	}

	public void link(IJml2bConfiguration config, LinkContext lc)
		throws Jml2bException {
		LinkUtils.linkEnumeration(config, signature.elements(), lc);
	}

	public int linkStatements(IJml2bConfiguration config, LinkContext lc)
		throws Jml2bException {
		return LinkUtils.linkStatements(config, signature.elements(), lc);
	}

	/** return true if the parameters are compatibles with the given vector 
	 *  of Type. (that is, the types stored in types could be used as 
	 * parameters for calling the method)
	 */
	/*@
	  @ requires types != null;
	  @*/
	public boolean isCompatible(IJml2bConfiguration config, Vector types) throws Jml2bException {
		int count = types.size();
		if (count != signature.size()) {
			// two signatures cannot be compatible if the number of arguments
			// is different
			return false;
		}

		/*@ 
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		for (int i = 0; i < count; ++i) {
			// get type of signature
			Field f = (Field) signature.get(i);
			Type signature_type = f.getType();
			// type of caller
			Type caller_type = (Type) types.get(i);

			if (!caller_type.isSubtypeOf(config, signature_type)) {
				return false;
			}
		}

		return true;
	}

	public Type getType(int i) {
		return getField(i).getType();
	}
	/** return true if all the types in this are compatible with the types
	 * in params.
	 */
	/*@
	  @ requires params != null;
	  @*/
	public boolean isCompatibleWith(
		IJml2bConfiguration config,
		IAParameters params) throws Jml2bException {
		int count = params.nparams();
		if (count != nparams()) {
			// two signatures cannot be compatible if the number of arguments
			// is different
			return false;
		}

		/*@ 
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		for (int i = 0; i < count; ++i) {
			// get type of this
			Type this_type = getField(i).getType();
			// type of caller
			Type param_type = params.getType(i);

			if (!this_type.isSubtypeOf(config, param_type)) {
				return false;
			}
		}

		return true;
	}

	/** compare the signature with the signature of the given parameters.
	 * return true iff the signature are the same. (does not check the
	 * names of parameters for equality).
	 */
	/*@
	  @ requires p != null;
	  @*/
	public boolean isSameAs(IAParameters p) {
		int count = nparams();

		if (count != p.nparams()) {
			return false;
		}

		/*@ 
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		for (int i = 0; i < count; ++i) {
			Type t1 = getField(i).getType();
			Type t2 = p.getType(i);

			if (!t1.equals(t2)) {
				return false;
			}
		}
		// if we reach this point, then both parameters have the same number
		// of elements, and have equal types.
		return true;
	}

	public Vector getSignature() {
		return signature;
	}

	public Field getField(int i) {
		return (Field) signature.get(i);
	}

	public int nparams() {
		return signature.size();
	}

	public Enumeration getParameters() {
		return signature.elements();
	}

	public String toString() {
		Enumeration e = getParameters();
		String res = "";
		/*@ 
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			res += f.getType().toString() + ";";
		}
		return res;
	}

	public String toString(char separator) {
		Enumeration e = getParameters();
		String res = "";
		boolean b = true;
		/*@ 
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			if (!f.garbage) {
				if (b)
					b = false;
				else
					res += separator;
				res += f.getBName();
			}
		}
		return res;
	}

	public String toJava() {
		Enumeration e = getParameters();
		boolean b = true;
		String res = "(";
		/*@ 
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		while (e.hasMoreElements()) {
			if (b)
				b = false;
			else
				res += ", ";
			Field f = (Field) e.nextElement();
			res += f.getType().toJava();
		}
		res += ")";
		return res;
	}

	public String toJavaWithParameterName() {
		Enumeration e = getParameters();
		boolean b = true;
		String res = "(";
		while (e.hasMoreElements()) {
			if (b)
				b = false;
			else
				res += ", ";
			Field f = (Field) e.nextElement();
			res += f.getType().toJava();
			res += " " + f.getName();
		}
		res += ")";
		return res;
	}

	void processIdent() {
		Enumeration e = signature.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.nameIndex = IdentifierResolver.addIdent(f);
		}
	}

	String emit() {
		boolean b = false;
		String s = "";
		Enumeration e = signature.elements();
		while (e.hasMoreElements()) {
			Field element = (Field) e.nextElement();
			if (b)
				s += ",";
			else
				b = true;
			s += element.getType().toJava() + " " + element.getName();
		}
		return s;
	}

	static final long serialVersionUID = 8346824517287613664L;

}
