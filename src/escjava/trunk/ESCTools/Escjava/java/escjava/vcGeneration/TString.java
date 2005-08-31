package escjava.vcGeneration;

class TString extends TLiteral{

    protected String value;

    protected TString (String value){
	this.value = value;
	type = $String;
    }

    public /*@ non_null @*/ StringBuffer toDot(){

	StringBuffer r = super.toDot();

	r.append("\\]\\n"+value);
	r.append("\"];\n");
	
	return r;
    }

}

