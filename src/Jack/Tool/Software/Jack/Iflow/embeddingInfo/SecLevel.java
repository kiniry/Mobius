package embeddingInfo;
/*
 * Created on Jan 14, 2005
 * @version $Id: SecLevel.java,v 1.3 2005/03/21 09:36:38 lmartini Exp $
 */

/**
 * @author Luca Martini
 *
 */


public abstract class SecLevel implements InterfaceSecLevel {
    public byte level;
    public byte levelArray;
    public boolean isArray=false;

    public SecLevel(byte level){
	this.level = level;
    }    
    
    public SecLevel(byte level, boolean _isArray){
	this.level = level;
	if (_isArray) {
	    levelArray = level;
	    isArray = true;
	}
	
    }    
    
    /**
     * <code>lub</code> method performs the least upperbound between
     * the object and the level passed as parameter.
     * 
     * @param sl the <code>SecLevel</code> that we want to calculate
     * the least upper bound with
     * @return a new <code>SecLevel</code> value holding the result
     */
    public abstract SecLevel lub(SecLevel sl);


    /**
     * <code>sup</code> method is very similar to the 
     * <code>lub</code>,
     * but performs the least upper bound in place, modifying and
     * returning <code>this</code>.
     *
     * @param sl the <code>SecLevel</code> that we want to calculate
     * the least upper bound with
     * @return <code>this</code>
     */
    public abstract SecLevel sup(SecLevel sl);
    
    public abstract boolean leq(SecLevel sl);
    public abstract boolean leqA(SecLevel sl);
    
    /**
     * Retrieve a String representation of this object
     * 
     * @return a <code>String</code> representation of this object.
     * @see Object#toString()
     */
    public String toString() {
	Byte b = new Byte(level);
	return b.toString();
    }
    
    public boolean equals(SecLevel s) {
	return ((level == s.level) && (isArray == s.isArray) &&
		(levelArray == s.levelArray));
    }
					
    
    /**
     * This methods checks if the <code>SecLevel</code> passed as
     * parameter has the same level for the arrat part.
     */
    public boolean equalsArray(SecLevel s) {
	return ((isArray == s.isArray) && (levelArray == s.levelArray));
    }
	
    public abstract Object clone();
}

    

