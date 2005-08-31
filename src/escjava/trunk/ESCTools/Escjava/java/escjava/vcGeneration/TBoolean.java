package escjava.vcGeneration;

class TBoolean extends TLiteral{

    protected boolean value;

    protected TBoolean (boolean value){
	this.value = value;
	type = $boolean;
    }

    public /*@ non_null @*/ StringBuffer toDot(){

	StringBuffer r = super.toDot();

	r.append("\\]\\n"+Boolean.toString(value));
	r.append("\"];\n");
	
	return r;
    }

}

