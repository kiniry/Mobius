package embeddingInfo;
/*
 * Created on Jan 14, 2005
 * @version $Id: HL.java,v 1.3 2005/03/21 09:36:38 lmartini Exp $
 */

/**
 * @author Luca Martini
 *
 */


public class HL extends SecLevel {
    public static byte H = (byte) (0x01);
    public static byte L = (byte) (0x00);
    private static final HL H_ = new HL(H,false);
    private static final HL L_ = new HL(L,false);

    public HL() {
	super(L);
    }
    
    public HL(byte level, boolean isarray){
	super(level,isarray);
    }    
    
    public HL(String levelstr, boolean isarray) {
	super(L,isarray);
	if (levelstr.equals("H")) {
	    level=H;
	    levelArray = H;

	}
	if (isarray)
	    isArray = true;
    }
    
    public HL(String levelstr) {
	super(L);
	if (levelstr.equals("H")) {
	    level=H;
	}
    }
    
    public SecLevel top() {
	return H_;
    }
    
    public SecLevel bottom(){
	return L_;
    }
    
    /* preserve the array status of this */
    public SecLevel lub(SecLevel sl) {
	SecLevel ret;
	if ((this.level+sl.level)== L) {
	    ret = new HL(L,this.isArray);
	    ret.levelArray = this.levelArray;
	} else {
	    ret = new HL(H,this.isArray);
	    ret.levelArray = this.levelArray;
	}
	return ret;
    }
    
    /* does not preserve isArray */
    public SecLevel sup(SecLevel sl) {
	if ((this.level+sl.level)!= L)
	    this.level = H;
	return this;
    }
    
    /* does not check isArray */
    public boolean leq(SecLevel sl) {
	return (level <= sl.level);
    }

    /* compare the level of the object with level of the array of the
     * parameter */
    public boolean leqA(SecLevel sl) {
	return (level <= sl.levelArray);
    }
    
    public String toString() {
	String ret = "";
	if (level==H)
	    ret+="H";
	else if (level == L) 
	    ret+="L";
	else 
	    ret+="?";
	if (isArray) {
	    ret+="[";
	    if (levelArray==H)
		ret+="H]";
	    else if (levelArray == L) 
		ret+="L]";
	    else 
		ret+="?]";
	}
	return ret;
    }
	
    public Object clone() {
	HL ret = new HL(level,isArray);
	ret.levelArray = levelArray;
	return ret;
    }

    public static void main(String[] args) {
	HL h = new HL("H",true);
	HL l = new HL("L",true);
	System.out.println("Top= " + h.top() );
	System.out.println("Bottom= " + h.bottom() );
	System.out.println("h= " + h );
	System.out.println("l= " + l );
	System.out.println("h+l= " + (h.lub(l)));
	System.out.println("h+h= " + (h.lub(h)));
	System.out.println("l+l= " + (l.lub(l)));
	System.out.println("l+h= " + (l.lub(h)));
	System.out.println("h<=l ? " + (h.leq(l)));
	System.out.println("h<=h ? " + (h.leq(h)));
	System.out.println("l<=l ? " + (l.leq(l)));
	System.out.println("l<=h ? " + (l.leq(h)));
	System.out.println("l.sup(l)= " + l.sup(l) );
	System.out.println("l.sup(h)= " + l.sup(h) );
    } // end of main()
    
}

    

