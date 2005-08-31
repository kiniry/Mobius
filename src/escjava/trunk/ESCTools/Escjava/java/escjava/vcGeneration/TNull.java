package escjava.vcGeneration;

class TNull extends TLiteral {
    
    protected Object value = null;
    
    protected TNull(){
	type = $Reference;
    }

    public /*@ non_null @*/ StringBuffer toDot(){

	StringBuffer r = super.toDot();

	r.append("\\]\\nnull\"];\n");
	
	return r;
    }

}

