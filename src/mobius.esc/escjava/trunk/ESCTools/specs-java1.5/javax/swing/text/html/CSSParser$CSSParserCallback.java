package javax.swing.text.html;

import java.io.*;

interface CSSParser$CSSParserCallback {
    
    void handleImport(String importString);
    
    void handleSelector(String selector);
    
    void startRule();
    
    void handleProperty(String property);
    
    void handleValue(String value);
    
    void endRule();
}
