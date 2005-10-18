package escjava.vcGeneration;

class TString extends TLiteral{

    protected String value;

    protected TString (String value){
	this.value = value;
	type = $String;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTString(this);
    }

}

class TBoolean extends TLiteral{

    protected boolean value;

    protected TBoolean (boolean value){
	this.value = value;
	type = $boolean;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTBoolean(this);
    }

}

class TChar extends TLiteral{

    protected char value;

    protected TChar (int value){
	this.value = (char)value;
	type = $char;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTChar(this);
    }

}

class TInt extends TLiteral {
    
    protected int value;
    
    protected TInt(int value){
	this.value = value;
	type = $integer;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTInt(this);
    }

}

class TFloat extends TLiteral {
    
    protected  float value;
    
    protected TFloat(float value){
	this.value = value;
	type = $float;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloat(this);
    }

}

class TDouble extends TLiteral {
    
    protected  double value;
    
    protected TDouble(double value){
	this.value = value;
	type = $float;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTDouble(this);
    }

}

class TNull extends TLiteral {
    
    protected Object value = null;
    
    protected TNull(){
	type = $Reference;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTNull(this);
    }

}

