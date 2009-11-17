package java.beans;

import java.applet.Applet;
import java.beans.beancontext.BeanContext;

public interface AppletInitializer {
    
    void initialize(Applet newAppletBean, BeanContext bCtxt);
    
    void activate(Applet newApplet);
}
