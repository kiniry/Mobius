/*
 * Created on Jul 9, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcclass.attributes;
/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class LoopSpecification implements BCAttribute {
	SingleLoopSpecification[] loopSpecs;
	
	public LoopSpecification(SingleLoopSpecification[] _loopSpecs) {
		loopSpecs = _loopSpecs;
	}

	/**
	 * @return
	 */
	public SingleLoopSpecification[] getLoopSpecifications() {
		return loopSpecs;
	}
}
