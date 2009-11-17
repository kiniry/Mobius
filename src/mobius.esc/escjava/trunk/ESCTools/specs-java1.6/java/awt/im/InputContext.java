package java.awt.im;

import java.awt.Component;
import java.util.Locale;
import java.awt.AWTEvent;
import java.lang.Character.Subset;

public class InputContext {
    
    protected InputContext() {
        
    }
    
    public static InputContext getInstance() {
        return new sun.awt.im.InputMethodContext();
    }
    
    public boolean selectInputMethod(Locale locale) {
        return false;
    }
    
    public Locale getLocale() {
        return null;
    }
    
    public void setCharacterSubsets(Character$Subset[] subsets) {
    }
    
    public void setCompositionEnabled(boolean enable) {
    }
    
    public boolean isCompositionEnabled() {
        return false;
    }
    
    public void reconvert() {
    }
    
    public void dispatchEvent(AWTEvent event) {
    }
    
    public void removeNotify(Component client) {
    }
    
    public void endComposition() {
    }
    
    public void dispose() {
    }
    
    public Object getInputMethodControlObject() {
        return null;
    }
}
