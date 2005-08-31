package escjava.vcGeneration;

class TChar extends TLiteral{

    protected char value;

    protected TChar (int value){
	this.value = (char)value;
	type = $char;
    }

    public /*@ non_null @*/ StringBuffer toDot(){

	StringBuffer r = super.toDot();

	r.append("\\]\\n"+Character.toString(value));
	r.append("\"];\n");
	
	return r;
    }

}

