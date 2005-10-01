package escjava.vcGeneration;
import java.lang.StringBuffer;

// fuck the fact that 'StrinBuffer' is final
class SimplifyStringBuffer {

    /*@ non_null @*/ StringBuffer out = null;
    /*@ non_null @*/ StringBuffer indentation = null;

    SimplifyStringBuffer(){
	out = new StringBuffer();
	indentation = new StringBuffer();
    }

    /*
     * just append the parameter, N = normal
     */
    /*@ non_null @*/ StringBuffer appendN(/*@ non_null @*/ String s){
	out.append(s);

	return out;
    }
    
    /*
     * append indentation and parameter
     */
    /*@ non_null @*/ StringBuffer append(/*@ non_null @*/ String s){
	out.append(indentation);
	out.append(s);

	return out;
    }

    /*
     * This function goes to next line, increases indentation by two spaces
     * and add a '('
     * If you want to change the indentation style do it here.
     */ 
    /*@ non_null @*/ StringBuffer appendI(/*@ non_null @*/ String s){

	if(indentation.length() != 0){ // not first call
	    out.append("\n");
	    out.append(indentation);
	}

	indentation.append("  ");

	out.append("("+s);

	return out;
    }

    /*
     * This function goes to next line, increases indentation by two spaces
     * and add a '('
     * If you want to change the indentation style do it here.
     */ 
    /*@ non_null @*/ StringBuffer appendIwNl(/*@ non_null @*/ String s){
	indentation.append("  ");
	out.append(indentation);
	out.append("("+s);

	return out;
    }

    /*
     * This function goes to new line, add a ')' and
     * reduces indentation by two spaces
     * If you want to change the indentation style do it here.
     */ 
    /*@ non_null @*/ StringBuffer reduceI(){
	out.append("\n");
	out.append(indentation+")"); 
	indentation = indentation.delete(0,2);
	
	return out;
    }

    /*
     * This function add a ')' and
     * reduces indentation by two spaces
     * If you want to change the indentation style do it here.
     */ 
    /*@ non_null @*/ StringBuffer reduceIwNl(){
 	out.append(")");
 	indentation = indentation.delete(0,2);
	
	return out;
    }

    public /*@ non_null @*/ String toString(){
	return out.toString();
    }

}
