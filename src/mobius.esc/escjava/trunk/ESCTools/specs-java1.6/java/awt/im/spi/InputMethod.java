package java.awt.im.spi;

import java.util.Locale;
import java.awt.AWTEvent;
import java.awt.Rectangle;
import java.lang.Character.Subset;

public interface InputMethod {
    
    public void setInputMethodContext(InputMethodContext context);
    
    public boolean setLocale(Locale locale);
    
    public Locale getLocale();
    
    public void setCharacterSubsets(Character$Subset[] subsets);
    
    public void setCompositionEnabled(boolean enable);
    
    public boolean isCompositionEnabled();
    
    public void reconvert();
    
    public void dispatchEvent(AWTEvent event);
    
    public void notifyClientWindowChange(Rectangle bounds);
    
    public void activate();
    
    public void deactivate(boolean isTemporary);
    
    public void hideWindows();
    
    public void removeNotify();
    
    public void endComposition();
    
    public void dispose();
    
    public Object getControlObject();
}
