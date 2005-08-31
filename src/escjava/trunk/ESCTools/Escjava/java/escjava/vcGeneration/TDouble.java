package escjava.vcGeneration;

class TDouble extends TLiteral {
    
    protected  double value;
    
    protected TDouble(double value){
	this.value = value;
	type = $float;
    }

    public /*@ non_null @*/ StringBuffer toDot(){

	StringBuffer r = super.toDot();

	r.append("\\]\\n"+Double.toString(value));
	r.append("\"];\n");
	
	return r;
    }

}

