package javax.swing.text.html;

import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.border.*;
import javax.swing.text.*;

class StyleSheet$SearchBuffer {
    
    private StyleSheet$SearchBuffer() {
        
    }
    static Stack searchBuffers = new Stack();
    Vector vector = null;
    StringBuffer stringBuffer = null;
    Hashtable hashtable = null;
    
    static StyleSheet$SearchBuffer obtainSearchBuffer() {
        StyleSheet$SearchBuffer sb;
        try {
            if (!searchBuffers.empty()) {
                sb = (StyleSheet$SearchBuffer)(StyleSheet$SearchBuffer)searchBuffers.pop();
            } else {
                sb = new StyleSheet$SearchBuffer();
            }
        } catch (EmptyStackException ese) {
            sb = new StyleSheet$SearchBuffer();
        }
        return sb;
    }
    
    static void releaseSearchBuffer(StyleSheet$SearchBuffer sb) {
        sb.empty();
        searchBuffers.push(sb);
    }
    
    StringBuffer getStringBuffer() {
        if (stringBuffer == null) {
            stringBuffer = new StringBuffer();
        }
        return stringBuffer;
    }
    
    Vector getVector() {
        if (vector == null) {
            vector = new Vector();
        }
        return vector;
    }
    
    Hashtable getHashtable() {
        if (hashtable == null) {
            hashtable = new Hashtable();
        }
        return hashtable;
    }
    
    void empty() {
        if (stringBuffer != null) {
            stringBuffer.setLength(0);
        }
        if (vector != null) {
            vector.removeAllElements();
        }
        if (hashtable != null) {
            hashtable.clear();
        }
    }
}
