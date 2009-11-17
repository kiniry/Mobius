package javax.swing.event;

import java.util.EventObject;
import java.net.URL;
import javax.swing.text.Element;

public class HyperlinkEvent extends EventObject {
    
    public HyperlinkEvent(Object source, HyperlinkEvent$EventType type, URL u) {
        this(source, type, u, null);
    }
    
    public HyperlinkEvent(Object source, HyperlinkEvent$EventType type, URL u, String desc) {
        this(source, type, u, desc, null);
    }
    
    public HyperlinkEvent(Object source, HyperlinkEvent$EventType type, URL u, String desc, Element sourceElement) {
        super(source);
        this.type = type;
        this.u = u;
        this.desc = desc;
        this.sourceElement = sourceElement;
    }
    
    public HyperlinkEvent$EventType getEventType() {
        return type;
    }
    
    public String getDescription() {
        return desc;
    }
    
    public URL getURL() {
        return u;
    }
    
    public Element getSourceElement() {
        return sourceElement;
    }
    private HyperlinkEvent$EventType type;
    private URL u;
    private String desc;
    private Element sourceElement;
    {
    }
}
