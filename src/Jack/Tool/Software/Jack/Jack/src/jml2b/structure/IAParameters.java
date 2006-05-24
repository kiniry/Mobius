/*
 * Created on Apr 27, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.java.Type;

/**
 *
 *  @author L. Burdy
 **/
public abstract class IAParameters {

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
			Type t1 = getType(i);
			Type t2 = p.getType(i);

			if (!t1.equals(t2)) {
				return false;
			}
		}
		// if we reach this point, then both parameters have the same number
		// of elements, and have equal types.
		return true;
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
			Type this_type = getType(i);
			// type of caller
			Type param_type = params.getType(i);

			if (!this_type.isSubtypeOf(config, param_type)) {
				return false;
			}
		}

		return true;
	}


	/** compare the signature with the given vector of types.
	 *  return true iff the signatures are equals.
	 */
	/*@
	  @ requires types != null;
	  @*/
	public boolean hasSameTypes(Vector types) {
		int count = nparams();

		if (count != types.size()) {
			return false;
		}

		/*@ 
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		for (int i = 0; i < count; ++i) {
			Type t1 = getType(i);
			Type t2 = (Type) types.get(i);

			if (!t1.equals(t2)) {
				return false;
			}
		}

		return true;
	}
	

	/**
	 * @return
	 */
	public abstract int nparams();

	/** return true if the parameters are compatibles with the given vector 
	 *  of Type. (that is, the types stored in types could be used as 
	 * parameters for calling the method)
	 */
	/*@
	  @ requires types != null;
	  @*/
	public boolean isCompatible(IJml2bConfiguration config, Vector types) throws Jml2bException {
		int count = types.size();
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
			// get type of signature
			Type signature_type = getType(i);
			// type of caller
			Type caller_type = (Type) types.get(i);

			if (!caller_type.isSubtypeOf(config, signature_type)) {
				return false;
			}
		}

		return true;
	}


	/**
	 * @param config TODO
	 * @param c
	 * @return
	 */
	public abstract String toString(char c);

	/**
	 * @param i
	 * @return
	 */
	public abstract Type getType(int i);

}
