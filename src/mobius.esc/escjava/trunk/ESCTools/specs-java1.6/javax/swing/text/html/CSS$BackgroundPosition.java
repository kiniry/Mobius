package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$BackgroundPosition extends CSS$CssValue {
    
    CSS$BackgroundPosition() {
        
    }
    float horizontalPosition;
    float verticalPosition;
    short relative;
    
    Object parseCssValue(String value) {
        String[] strings = CSS.parseStrings(value);
        int count = strings.length;
        CSS$BackgroundPosition bp = new CSS$BackgroundPosition();
        bp.relative = 5;
        bp.svalue = value;
        if (count > 0) {
            short found = 0;
            int index = 0;
            while (index < count) {
                String string = strings[index++];
                if (string.equals("center")) {
                    found |= 4;
                    continue;
                } else {
                    if ((found & 1) == 0) {
                        if (string.equals("top")) {
                            found |= 1;
                        } else if (string.equals("bottom")) {
                            found |= 1;
                            bp.verticalPosition = 1;
                            continue;
                        }
                    }
                    if ((found & 2) == 0) {
                        if (string.equals("left")) {
                            found |= 2;
                            bp.horizontalPosition = 0;
                        } else if (string.equals("right")) {
                            found |= 2;
                            bp.horizontalPosition = 1;
                        }
                    }
                }
            }
            if (found != 0) {
                if ((found & 1) == 1) {
                    if ((found & 2) == 0) {
                        bp.horizontalPosition = 0.5F;
                    }
                } else if ((found & 2) == 2) {
                    bp.verticalPosition = 0.5F;
                } else {
                    bp.horizontalPosition = bp.verticalPosition = 0.5F;
                }
            } else {
                CSS$LengthUnit lu = new CSS$LengthUnit(strings[0], (short)0, 0.0F);
                if (lu.type == 0) {
                    bp.horizontalPosition = lu.value;
                    bp.relative = (short)(1 ^ bp.relative);
                } else if (lu.type == 1) {
                    bp.horizontalPosition = lu.value;
                } else if (lu.type == 3) {
                    bp.horizontalPosition = lu.value;
                    bp.relative = (short)((1 ^ bp.relative) | 2);
                }
                if (count > 1) {
                    lu = new CSS$LengthUnit(strings[1], (short)0, 0.0F);
                    if (lu.type == 0) {
                        bp.verticalPosition = lu.value;
                        bp.relative = (short)(4 ^ bp.relative);
                    } else if (lu.type == 1) {
                        bp.verticalPosition = lu.value;
                    } else if (lu.type == 3) {
                        bp.verticalPosition = lu.value;
                        bp.relative = (short)((4 ^ bp.relative) | 8);
                    }
                } else {
                    bp.verticalPosition = 0.5F;
                }
            }
        }
        return bp;
    }
    
    boolean isHorizontalPositionRelativeToSize() {
        return ((relative & 1) == 1);
    }
    
    boolean isHorizontalPositionRelativeToFontSize() {
        return ((relative & 2) == 2);
    }
    
    float getHorizontalPosition() {
        return horizontalPosition;
    }
    
    boolean isVerticalPositionRelativeToSize() {
        return ((relative & 4) == 4);
    }
    
    boolean isVerticalPositionRelativeToFontSize() {
        return ((relative & 8) == 8);
    }
    
    float getVerticalPosition() {
        return verticalPosition;
    }
}
