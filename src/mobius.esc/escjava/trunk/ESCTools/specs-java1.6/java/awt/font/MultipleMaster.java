package java.awt.font;

import java.awt.Font;

public interface MultipleMaster {
    
    public int getNumDesignAxes();
    
    public float[] getDesignAxisRanges();
    
    public float[] getDesignAxisDefaults();
    
    public String[] getDesignAxisNames();
    
    public Font deriveMMFont(float[] axes);
    
    public Font deriveMMFont(float[] glyphWidths, float avgStemWidth, float typicalCapHeight, float typicalXHeight, float italicAngle);
}
