package java.awt.im.spi;

import java.awt.AWTException;
import java.awt.Image;
import java.util.Locale;

public interface InputMethodDescriptor {
    
    Locale[] getAvailableLocales() throws AWTException;
    
    boolean hasDynamicLocaleList();
    
    String getInputMethodDisplayName(Locale inputLocale, Locale displayLanguage);
    
    Image getInputMethodIcon(Locale inputLocale);
    
    InputMethod createInputMethod() throws Exception;
}
