package escjava.vcGeneration.coq;
import java.lang.StringBuffer;

/**
 * This class should maybe be replaced by the StringBufferWrapper.
 * @author J. Charles based on the old PvsStringBuffer from C. Hurlin. 
 * @version 14/11/2005
 */
public class CoqStringBuffer {

    /*@ non_null @*/ StringBuffer out = null;
    /*@ non_null @*/ StringBuffer indentation = null;


    /**
     * Construct a new, default CoqStringBuffer object
     */
    public CoqStringBuffer(){
    	this(null);
    }

    /**
     * Construct a new CoqStringBuffer object using o as the internal 
     * StringBuffer.
     * @param o The internal StringBuffer to rightly indent.
     */
    public CoqStringBuffer(StringBuffer o){
    	if(o == null)
    		out = new StringBuffer();
    	else
    		out = o;
    	indentation = new StringBuffer();
    }
    
    
    /**
     * just append the parameter, N stands for normal
     * @param s the String to append.
     * @return the resulting StringBuffer.
     */
    public /*@ non_null @*/ StringBuffer appendN(/*@ non_null @*/ String s){
	out.append(s);

	return out;
    }
    
    /**
     * append indentation and parameter
     * @param s the String to append.
     * @return the resulting StringBuffer.
     */
    public /*@ non_null @*/ StringBuffer append(/*@ non_null @*/ String s){
	out.append(indentation);
	out.append(s);

	return out;
    }

    /**
     * This function goes to next line, increases indentation by two spaces
     * and add a '('
     * If you want to change the indentation style do it here.
     * @param s the String to append.
     * @return the resulting StringBuffer.
     */ 
    public /*@ non_null @*/ StringBuffer appendI(/*@ non_null @*/ String s){

	if(indentation.length() != 0){ // not first call
	    out.append("\n");
	    out.append(indentation);
	}

	indentation.append("  ");

	out.append("("+s);

	return out;
    }

    /**
     * This function increases indentation by two spaces
     * and add a '('
     * If you want to change the indentation style do it here.
     * @param s the String to append.
     * @return the resulting StringBuffer.
     */ 
    public /*@ non_null @*/ StringBuffer appendIwNl(/*@ non_null @*/ String s){
	indentation.append("  ");
	out.append(indentation);
	out.append("("+s);

	return out;
    }

    /**
     * This function goes to new line, add a ')' and
     * reduces indentation by two spaces
     * If you want to change the indentation style do it here.
     * @return the resulting StringBuffer.
     */ 
    public /*@ non_null @*/ StringBuffer reduceI(){
	out.append("\n");
	indentation = indentation.delete(0,2);
	out.append(indentation+")"); 
		
	return out;
    }

    /**
     * This function add a ')' and
     * reduces indentation by two spaces
     * If you want to change the indentation style do it here.
     * @return the resulting StringBuffer.
     */ 
    public /*@ non_null @*/ StringBuffer reduceIwNl(){
 	out.append(")");
 	indentation = indentation.delete(0,2);
	
	return out;
    }

    /**
     * @return the {@link StringBuffer#toString() toString()}  of the current StringBuffer value.
     */
    public /*@ non_null @*/ String toString(){
    	return out.toString();
    }

}
