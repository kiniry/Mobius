package escjava.vcGeneration;

class TInt extends TLiteral {
    
    protected int value;
    
    protected TInt(int value){
	this.value = value;
	type = $integer;
    }

    public /*@ non_null @*/ StringBuffer toDot(){

	StringBuffer r = super.toDot();

	r.append("\\]\\n"+Integer.toString(value));
	r.append("\"];\n");
	
	return r;
    }

}

