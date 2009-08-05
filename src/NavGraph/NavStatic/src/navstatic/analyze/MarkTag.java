package navstatic.analyze;

import soot.tagkit.Tag;

public class MarkTag implements Tag {
    public static final String name = "MarkTag";
    final private int key;

    MarkTag(int key) { this.key = key; }
        
    public String getName() { return name; }
    
    /* This function is not used */
    public byte [] getValue() { 
    	byte [] o = new byte [3];
        o[0] = (byte) (key >> 16 & 0xff);
        o[1] = (byte) (key >> 8 & 0xff);
        o[2] = (byte) (key & 0xff);
        return o;
    }
    
    public int getMark() { return key; }
    

}
