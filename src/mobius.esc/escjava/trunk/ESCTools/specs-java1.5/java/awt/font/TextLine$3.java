package java.awt.font;

import sun.font.TextLineComponent;

class TextLine$3 extends TextLine$Function {
    
    TextLine$3() {
        super(null);
    }
    
    float computeFunction(TextLine line, int componentIndex, int indexInArray) {
        int vi = TextLine.access$200(line) == null ? componentIndex : TextLine.access$200(line)[componentIndex];
        TextLineComponent tlc = TextLine.access$100(line)[componentIndex];
        return TextLine.access$300(line)[vi * 2] + tlc.getCharX(indexInArray);
    }
}
