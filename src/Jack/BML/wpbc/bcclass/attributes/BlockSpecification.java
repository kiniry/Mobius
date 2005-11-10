/*
 * Created on Jul 9, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass.attributes;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BlockSpecification implements BCAttribute {
	private SingleBlockSpecification[] blockSpecifications;

	public BlockSpecification(SingleBlockSpecification[] _blockSpecifications){
		blockSpecifications = _blockSpecifications;
	}
	
	public SingleBlockSpecification[] getBlockSpecifications() {
		return blockSpecifications;
	}
}


