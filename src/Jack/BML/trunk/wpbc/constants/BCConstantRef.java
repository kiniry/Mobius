/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package constants;


/**
 * @author mpavlova
 *
 * the class represents a constant pool constant : either 
 * CONSTANT_Fieldref_info, CONSTANT_MethodRef_info, CONSTANT_Class_info 
 */
public class BCConstantRef extends BCConstant {
	private int classIndex;
	
	private int CONSTANT_class_Index;
	
	private String name;

	public BCConstantRef( ) {
	}
	
	public BCConstantRef( int CONSTANT_X_info_index, int _CONSTANT_class_Index , String _name) {
		super(CONSTANT_X_info_index);
		CONSTANT_class_Index = _CONSTANT_class_Index;
		name = _name;
	}
	
	public int getClassIndex() {
		return CONSTANT_class_Index;
	}	
	
	public String getName() {
		return name;
	}
}
