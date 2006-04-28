/*
 * Created on 2005-05-18
 */
package umbra.instructions;


/**
 * @author Tomek Batkiewicz i Jaros³aw Paszek
 */ 
public class CodeLineController extends BytecodeLineController {

	public CodeLineController(String l) {
		super(l);
	}

	private String dajs() {
	String s;
    s = "";
    int i = 0;
    int j = line.length();
    for (i = 0; i < j; i++)
    	if (!(Character.isWhitespace(line.charAt(i)))) {
    		s += line.charAt(i);
    	}
	return s;
	}
	public boolean correct()
	{   //Code musi byc bo by nie byla ta klasa
		if (this.line.startsWith("Code")) {
		if (!(line.indexOf("(") > 0))
			return false;
	    
		String s = dajs();
		int i = 0;
	    //czy jest to co trzeba
	    if (!(s.indexOf("max_stack=") > 0))
			return false;
	    if (!(s.indexOf(",max_locals=") > 0))
			return false;
	    if (!(s.indexOf(",code_length=") > 0))
			return false;
	    //czy liczby sa poprawne
	    for (i = (s.indexOf("max_stack=") + 10); i < (s.indexOf(",max_locals="));i++) {
	    	if (!(Character.isDigit(s.charAt(i))))
	     	return false;
	    }
	    for (i = (s.indexOf(",max_locals=") + 12); i < (s.indexOf(",code_length="));i++) {
	    	if (!(Character.isDigit(s.charAt(i))))
	    		return false;
	    }
	    for (i = (s.indexOf(",code_length=") + 13); i < (s.indexOf(")"));i++) {
	    	if (!(Character.isDigit(s.charAt(i))))
	    		return false;
	    }
	    //czy kolejnosc ok - chyba po tym na dole niepotrzebne
	    if ((s.indexOf("Code")) > (s.indexOf("(")))
    		return false;
	    if ((s.indexOf("(")) > (s.indexOf("max_stack=")))
    		return false;
	    if ((s.indexOf("max_stack=")) > (s.indexOf(",max_locals=")))
    		return false;
	    if ((s.indexOf(",max_locals=")) > (s.indexOf(",code_length=")))
    		return false;
	    if ((s.indexOf(",code_length")) > (s.indexOf(")")))
    		return false;
	    //czy w ogole sa liczby
	    //System.out.println(s);
	    //System.out.println("dupa" + s.indexOf(",code_length"));
	    //System.out.println("blada" + s.indexOf(")"));
	    //System.out.println(s.length());
	    if (((s.indexOf("max_stack=")) + 11) > (s.indexOf(",max_locals=")))
    		return false;
	    if (((s.indexOf(",max_locals=")) + 13) > (s.indexOf(",code_length=")))
    		return false;
	    if ((s.indexOf(",code_length=")) + 14 > (s.indexOf(")")))
    		return false;
	    //czy nawiasy poprawnie tzn jak po ) cos to zle
	    if ((s.indexOf(")")) + 1 < (s.length()))
    		return false;
	    
        //	czy kolejnosc ok
	    if ((s.indexOf("Code")) < (s.indexOf("(")))
    		if ((s.indexOf("(")) < (s.indexOf("max_stack=")))
    			    if ((s.indexOf("max_stack=")) < (s.indexOf(",max_locals=")))
    			    	if ((s.indexOf(",max_locals=")) < (s.indexOf(",code_length=")))
    			    		if ((s.indexOf(",code_length")) < (s.indexOf(")")))
    			    			if ((s.indexOf("(")) < 5)
    			    				if ((s.indexOf("max_stack=")) < 6)
    			    					return true;
		}
		if (this.line.startsWith("LineNumber")) {
			return true;
		}
		if (this.line.startsWith("LocalVariable")) {
			String s = dajs();
			if ((s.indexOf("start_pc=")) > -1) {
				if ((s.indexOf("length=")) > -1) {
					if ((s.indexOf("index=")) > -1) {
						if ((line.indexOf("start_pc")) > -1) {
							if ((line.indexOf("length")) > -1) {
								if ((line.indexOf("index")) > -1) {
									return true;
								}
							}
						}
					}
				}
			}
		}
		if (this.line.startsWith("Attribute")) {
			String s = dajs();
			if ((s.indexOf("(s)=")) > -1) {
			  return true;
			}
			}
		
	    return false;
	}
}
