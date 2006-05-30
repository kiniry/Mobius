/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode;

import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public interface ByteCode  {
	
	/**
	 * @param config TODO
	 * @return the wp for this bytecode
	 */
	public Formula wp(IJml2bConfiguration config,   Formula _normal_Postcondition, ExsuresTable _exc_Postcondition );
	
	
	public VCGPath wp( IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) ;
}
