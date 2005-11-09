package escjava.vcGeneration;

import java.util.Vector;

public class TMethodCall extends TFunction {
	private VariableInfo name;
	private Vector argTypes = new Vector();
	public static Vector methNames = new Vector();
	public static Vector methDefs = new Vector();
	/**
	 * @param args
	 */ 
	public void accept(/*@ non_null @*/ TVisitor v){
			v.visitTMethodCall(this);
	}
	public TMethodCall(/*@ non_null @*/ String name) {
		this.name = new VariableInfo(name, new TypeInfo("pure method"));
		if(!methNames.contains(this.name)) {
			methNames.add(this.name);
			methDefs.add(this);
		}
	}
	public VariableInfo getName() {
		return name;
	}
    protected void typeTree(){

    	/*
    	 * Semantic control : for now we determine the type of the pure method
    	 */
    	
    	for(int i = 0; i < sons.size(); i++){
    	    TNode nodeTemp = getChildAt(i);
    	    nodeTemp.typeTree();
    	    argTypes.add(nodeTemp.type);
    	}

    }
    public Vector getArgType() {
    	return argTypes;
    }
    protected void setType(TypeInfo type, boolean sure){
        	this.type = type;
    }
}
