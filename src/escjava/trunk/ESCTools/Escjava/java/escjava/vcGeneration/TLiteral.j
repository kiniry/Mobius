package escjava.vcGeneration;

public class TString extends TLiteral{

    public String value;

    protected TString (String value){
	this.value = value;
	type = $String;
    }

    public void accept(/*@ non_null @*/ TVisitor v) throws java.io.IOException{
	v.visitTString(this);
    }

}

public class TBoolean extends TLiteral{

    public boolean value;

    protected TBoolean (boolean value){
	this.value = value;
	type = $boolean;
    }

    public void accept(/*@ non_null @*/ TVisitor v) throws java.io.IOException{
	v.visitTBoolean(this);
    }

}

public class TChar extends TLiteral{

    public char value;

    protected TChar (int value){
	this.value = (char)value;
	type = $char;
    }

    public void accept(/*@ non_null @*/ TVisitor v) throws java.io.IOException{
	v.visitTChar(this);
    }

}

public class TInt extends TLiteral {
    
    public int value;
    
    protected TInt(int value){
	this.value = value;
	type = $integer;
    }

    public void accept(/*@ non_null @*/ TVisitor v) throws java.io.IOException{
	v.visitTInt(this);
    }

}

public class TFloat extends TLiteral {
    
    public  float value;
    
    protected TFloat(float value){
	this.value = value;
	type = $float;
    }

    public void accept(/*@ non_null @*/ TVisitor v) throws java.io.IOException{
	v.visitTFloat(this);
    }

}

public class TDouble extends TLiteral {
    
    public  double value;
    
    protected TDouble(double value){
	this.value = value;
	type = $float;
    }

    public void accept(/*@ non_null @*/ TVisitor v) throws java.io.IOException{
	v.visitTDouble(this);
    }

}

public class TNull extends TLiteral {
    
    protected Object value = null;
    
    protected TNull(){
	type = $Reference;
    }

    public void accept(/*@ non_null @*/ TVisitor v) throws java.io.IOException{
	v.visitTNull(this);
    }

}

