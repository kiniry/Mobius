package escjava.vcGeneration;

class TFloat extends TLiteral {
    
    protected  float value;
    
    protected TFloat(float value){
	this.value = value;
	type = $float;
    }

    public /*@ non_null @*/ StringBuffer toDot(){

	StringBuffer r = super.toDot();

	r.append("\\]\\n"+Float.toString(value));
	r.append("\"];\n");
	
	return r;
    }

}

