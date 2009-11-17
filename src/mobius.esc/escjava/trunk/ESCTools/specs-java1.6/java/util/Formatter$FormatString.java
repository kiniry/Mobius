package java.util;

import java.io.IOException;
import java.util.Locale;

interface Formatter$FormatString {
    
    int index();
    
    void print(Object arg, Locale l) throws IOException;
    
    String toString();
}
