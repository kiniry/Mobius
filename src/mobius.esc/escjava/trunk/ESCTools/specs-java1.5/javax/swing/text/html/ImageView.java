package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.ImageObserver;
import java.io.*;
import java.net.*;
import java.util.Dictionary;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.event.*;

public class ImageView extends View {
    
    /*synthetic*/ static int access$900() {
        return sIncRate;
    }
    
    /*synthetic*/ static boolean access$800() {
        return sIsInc;
    }
    
    /*synthetic*/ static void access$700(ImageView x0) {
        x0.updateAltTextView();
    }
    
    /*synthetic*/ static int access$602(ImageView x0, int x1) {
        return x0.height = x1;
    }
    
    /*synthetic*/ static int access$502(ImageView x0, int x1) {
        return x0.width = x1;
    }
    
    /*synthetic*/ static int access$400(ImageView x0) {
        return x0.state;
    }
    
    /*synthetic*/ static void access$300(ImageView x0, long x1) {
        x0.repaint(x1);
    }
    
    /*synthetic*/ static Image access$202(ImageView x0, Image x1) {
        return x0.image = x1;
    }
    
    /*synthetic*/ static Image access$200(ImageView x0) {
        return x0.image;
    }
    
    /*synthetic*/ static void access$100(ImageView x0) {
        x0.safePreferenceChanged();
    }
    private static boolean sIsInc = false;
    private static int sIncRate = 100;
    private static Icon sPendingImageIcon;
    private static Icon sMissingImageIcon;
    private static final String PENDING_IMAGE_SRC = "icons/image-delayed.gif";
    private static final String MISSING_IMAGE_SRC = "icons/image-failed.gif";
    private static final String IMAGE_CACHE_PROPERTY = "imageCache";
    private static final int DEFAULT_WIDTH = 38;
    private static final int DEFAULT_HEIGHT = 38;
    private static final int DEFAULT_BORDER = 2;
    private static final int LOADING_FLAG = 1;
    private static final int LINK_FLAG = 2;
    private static final int WIDTH_FLAG = 4;
    private static final int HEIGHT_FLAG = 8;
    private static final int RELOAD_FLAG = 16;
    private static final int RELOAD_IMAGE_FLAG = 32;
    private static final int SYNC_LOAD_FLAG = 64;
    private AttributeSet attr;
    private Image image;
    private int width;
    private int height;
    private int state;
    private Container container;
    private Rectangle fBounds;
    private Color borderColor;
    private short borderSize;
    private short leftInset;
    private short rightInset;
    private short topInset;
    private short bottomInset;
    private ImageObserver imageObserver;
    private View altView;
    private float vAlign;
    
    public ImageView(Element elem) {
        super(elem);
        fBounds = new Rectangle();
        imageObserver = new ImageView$ImageHandler(this, null);
        state = RELOAD_FLAG | RELOAD_IMAGE_FLAG;
    }
    
    public String getAltText() {
        return (String)(String)getElement().getAttributes().getAttribute(HTML$Attribute.ALT);
    }
    
    public URL getImageURL() {
        String src = (String)(String)getElement().getAttributes().getAttribute(HTML$Attribute.SRC);
        if (src == null) {
            return null;
        }
        URL reference = ((HTMLDocument)(HTMLDocument)getDocument()).getBase();
        try {
            URL u = new URL(reference, src);
            return u;
        } catch (MalformedURLException e) {
            return null;
        }
    }
    
    public Icon getNoImageIcon() {
        loadDefaultIconsIfNecessary();
        return sMissingImageIcon;
    }
    
    public Icon getLoadingImageIcon() {
        loadDefaultIconsIfNecessary();
        return sPendingImageIcon;
    }
    
    public Image getImage() {
        sync();
        return image;
    }
    
    public void setLoadsSynchronously(boolean newValue) {
        synchronized (this) {
            if (newValue) {
                state |= SYNC_LOAD_FLAG;
            } else {
                state = (state | SYNC_LOAD_FLAG) ^ SYNC_LOAD_FLAG;
            }
        }
    }
    
    public boolean getLoadsSynchronously() {
        return ((state & SYNC_LOAD_FLAG) != 0);
    }
    
    protected StyleSheet getStyleSheet() {
        HTMLDocument doc = (HTMLDocument)(HTMLDocument)getDocument();
        return doc.getStyleSheet();
    }
    
    public AttributeSet getAttributes() {
        sync();
        return attr;
    }
    
    public String getToolTipText(float x, float y, Shape allocation) {
        return getAltText();
    }
    
    protected void setPropertiesFromAttributes() {
        StyleSheet sheet = getStyleSheet();
        this.attr = sheet.getViewAttributes(this);
        borderSize = (short)getIntAttr(HTML$Attribute.BORDER, isLink() ? DEFAULT_BORDER : 0);
        leftInset = rightInset = (short)(getIntAttr(HTML$Attribute.HSPACE, 0) + borderSize);
        topInset = bottomInset = (short)(getIntAttr(HTML$Attribute.VSPACE, 0) + borderSize);
        borderColor = ((StyledDocument)(StyledDocument)getDocument()).getForeground(getAttributes());
        AttributeSet attr = getElement().getAttributes();
        Object alignment = attr.getAttribute(HTML$Attribute.ALIGN);
        vAlign = 1.0F;
        if (alignment != null) {
            alignment = alignment.toString();
            if ("top".equals(alignment)) {
                vAlign = 0.0F;
            } else if ("middle".equals(alignment)) {
                vAlign = 0.5F;
            }
        }
        AttributeSet anchorAttr = (AttributeSet)(AttributeSet)attr.getAttribute(HTML$Tag.A);
        if (anchorAttr != null && anchorAttr.isDefined(HTML$Attribute.HREF)) {
            synchronized (this) {
                state |= LINK_FLAG;
            }
        } else {
            synchronized (this) {
                state = (state | LINK_FLAG) ^ LINK_FLAG;
            }
        }
    }
    
    public void setParent(View parent) {
        View oldParent = getParent();
        super.setParent(parent);
        container = (parent != null) ? getContainer() : null;
        if (oldParent != parent) {
            synchronized (this) {
                state |= RELOAD_FLAG;
            }
        }
    }
    
    public void changedUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        super.changedUpdate(e, a, f);
        synchronized (this) {
            state |= RELOAD_FLAG | RELOAD_IMAGE_FLAG;
        }
        preferenceChanged(null, true, true);
    }
    
    public void paint(Graphics g, Shape a) {
        sync();
        Rectangle rect = (a instanceof Rectangle) ? (Rectangle)(Rectangle)a : a.getBounds();
        Image image = getImage();
        Rectangle clip = g.getClipBounds();
        fBounds.setBounds(rect);
        paintHighlights(g, a);
        paintBorder(g, rect);
        if (clip != null) {
            g.clipRect(rect.x + leftInset, rect.y + topInset, rect.width - leftInset - rightInset, rect.height - topInset - bottomInset);
        }
        if (image != null) {
            if (!hasPixels(image)) {
                Icon icon = (image == null) ? getNoImageIcon() : getLoadingImageIcon();
                if (icon != null) {
                    icon.paintIcon(getContainer(), g, rect.x + leftInset, rect.y + topInset);
                }
            } else {
                g.drawImage(image, rect.x + leftInset, rect.y + topInset, width, height, imageObserver);
            }
        } else {
            Icon icon = getNoImageIcon();
            if (icon != null) {
                icon.paintIcon(getContainer(), g, rect.x + leftInset, rect.y + topInset);
            }
            View view = getAltView();
            if (view != null && ((state & WIDTH_FLAG) == 0 || width > DEFAULT_WIDTH)) {
                Rectangle altRect = new Rectangle(rect.x + leftInset + DEFAULT_WIDTH, rect.y + topInset, rect.width - leftInset - rightInset - DEFAULT_WIDTH, rect.height - topInset - bottomInset);
                view.paint(g, altRect);
            }
        }
        if (clip != null) {
            g.setClip(clip.x, clip.y, clip.width, clip.height);
        }
    }
    
    private void paintHighlights(Graphics g, Shape shape) {
        if (container instanceof JTextComponent) {
            JTextComponent tc = (JTextComponent)(JTextComponent)container;
            Highlighter h = tc.getHighlighter();
            if (h instanceof LayeredHighlighter) {
                ((LayeredHighlighter)(LayeredHighlighter)h).paintLayeredHighlights(g, getStartOffset(), getEndOffset(), shape, tc, this);
            }
        }
    }
    
    private void paintBorder(Graphics g, Rectangle rect) {
        Color color = borderColor;
        if ((borderSize > 0 || image == null) && color != null) {
            int xOffset = leftInset - borderSize;
            int yOffset = topInset - borderSize;
            g.setColor(color);
            int n = (image == null) ? 1 : borderSize;
            for (int counter = 0; counter < n; counter++) {
                g.drawRect(rect.x + xOffset + counter, rect.y + yOffset + counter, rect.width - counter - counter - xOffset - xOffset - 1, rect.height - counter - counter - yOffset - yOffset - 1);
            }
        }
    }
    
    public float getPreferredSpan(int axis) {
        sync();
        if (axis == View.X_AXIS && (state & WIDTH_FLAG) == WIDTH_FLAG) {
            getPreferredSpanFromAltView(axis);
            return width + leftInset + rightInset;
        }
        if (axis == View.Y_AXIS && (state & HEIGHT_FLAG) == HEIGHT_FLAG) {
            getPreferredSpanFromAltView(axis);
            return height + topInset + bottomInset;
        }
        Image image = getImage();
        if (image != null) {
            switch (axis) {
            case View.X_AXIS: 
                return width + leftInset + rightInset;
            
            case View.Y_AXIS: 
                return height + topInset + bottomInset;
            
            default: 
                throw new IllegalArgumentException("Invalid axis: " + axis);
            
            }
        } else {
            View view = getAltView();
            float retValue = 0.0F;
            if (view != null) {
                retValue = view.getPreferredSpan(axis);
            }
            switch (axis) {
            case View.X_AXIS: 
                return retValue + (float)(width + leftInset + rightInset);
            
            case View.Y_AXIS: 
                return retValue + (float)(height + topInset + bottomInset);
            
            default: 
                throw new IllegalArgumentException("Invalid axis: " + axis);
            
            }
        }
    }
    
    public float getAlignment(int axis) {
        switch (axis) {
        case View.Y_AXIS: 
            return vAlign;
        
        default: 
            return super.getAlignment(axis);
        
        }
    }
    
    public Shape modelToView(int pos, Shape a, Position$Bias b) throws BadLocationException {
        int p0 = getStartOffset();
        int p1 = getEndOffset();
        if ((pos >= p0) && (pos <= p1)) {
            Rectangle r = a.getBounds();
            if (pos == p1) {
                r.x += r.width;
            }
            r.width = 0;
            return r;
        }
        return null;
    }
    
    public int viewToModel(float x, float y, Shape a, Position$Bias[] bias) {
        Rectangle alloc = (Rectangle)(Rectangle)a;
        if (x < alloc.x + alloc.width) {
            bias[0] = Position$Bias.Forward;
            return getStartOffset();
        }
        bias[0] = Position$Bias.Backward;
        return getEndOffset();
    }
    
    public void setSize(float width, float height) {
        sync();
        if (getImage() == null) {
            View view = getAltView();
            if (view != null) {
                view.setSize(Math.max(0.0F, width - (float)(DEFAULT_WIDTH + leftInset + rightInset)), Math.max(0.0F, height - (float)(topInset + bottomInset)));
            }
        }
    }
    
    private boolean isLink() {
        return ((state & LINK_FLAG) == LINK_FLAG);
    }
    
    private boolean hasPixels(Image image) {
        return image != null && (image.getHeight(imageObserver) > 0) && (image.getWidth(imageObserver) > 0);
    }
    
    private float getPreferredSpanFromAltView(int axis) {
        if (getImage() == null) {
            View view = getAltView();
            if (view != null) {
                return view.getPreferredSpan(axis);
            }
        }
        return 0.0F;
    }
    
    private Icon makeIcon(final String gifFile) throws IOException {
        InputStream resource = HTMLEditorKit.getResourceAsStream(gifFile);
        if (resource == null) {
            System.err.println(ImageView.class.getName() + "/" + gifFile + " not found.");
            return null;
        }
        BufferedInputStream in = new BufferedInputStream(resource);
        ByteArrayOutputStream out = new ByteArrayOutputStream(1024);
        byte[] buffer = new byte[1024];
        int n;
        while ((n = in.read(buffer)) > 0) {
            out.write(buffer, 0, n);
        }
        in.close();
        out.flush();
        buffer = out.toByteArray();
        if (buffer.length == 0) {
            System.err.println("warning: " + gifFile + " is zero-length");
            return null;
        }
        return new ImageIcon(buffer);
    }
    
    private void repaint(long delay) {
        if (container != null && fBounds != null) {
            container.repaint(delay, fBounds.x, fBounds.y, fBounds.width, fBounds.height);
        }
    }
    
    private void loadDefaultIconsIfNecessary() {
        try {
            if (sPendingImageIcon == null) sPendingImageIcon = makeIcon(PENDING_IMAGE_SRC);
            if (sMissingImageIcon == null) sMissingImageIcon = makeIcon(MISSING_IMAGE_SRC);
        } catch (Exception x) {
            System.err.println("ImageView: Couldn\'t load image icons");
        }
    }
    
    private int getIntAttr(HTML$Attribute name, int deflt) {
        AttributeSet attr = getElement().getAttributes();
        if (attr.isDefined(name)) {
            int i;
            String val = (String)(String)attr.getAttribute(name);
            if (val == null) {
                i = deflt;
            } else {
                try {
                    i = Math.max(0, Integer.parseInt(val));
                } catch (NumberFormatException x) {
                    i = deflt;
                }
            }
            return i;
        } else return deflt;
    }
    
    private void sync() {
        int s = state;
        if ((s & RELOAD_IMAGE_FLAG) != 0) {
            refreshImage();
        }
        s = state;
        if ((s & RELOAD_FLAG) != 0) {
            synchronized (this) {
                state = (state | RELOAD_FLAG) ^ RELOAD_FLAG;
            }
            setPropertiesFromAttributes();
        }
    }
    
    private void refreshImage() {
        synchronized (this) {
            state = (state | LOADING_FLAG | RELOAD_IMAGE_FLAG | WIDTH_FLAG | HEIGHT_FLAG) ^ (WIDTH_FLAG | HEIGHT_FLAG | RELOAD_IMAGE_FLAG);
            image = null;
            width = height = 0;
        }
        try {
            loadImage();
            updateImageSize();
        } finally {
            synchronized (this) {
                state = (state | LOADING_FLAG) ^ LOADING_FLAG;
            }
        }
    }
    
    private void loadImage() {
        URL src = getImageURL();
        Image newImage = null;
        if (src != null) {
            Dictionary cache = (Dictionary)(Dictionary)getDocument().getProperty(IMAGE_CACHE_PROPERTY);
            if (cache != null) {
                newImage = (Image)(Image)cache.get(src);
            } else {
                newImage = Toolkit.getDefaultToolkit().createImage(src);
                if (newImage != null && getLoadsSynchronously()) {
                    ImageIcon ii = new ImageIcon();
                    ii.setImage(newImage);
                }
            }
        }
        image = newImage;
    }
    
    private void updateImageSize() {
        int newWidth = 0;
        int newHeight = 0;
        int newState = 0;
        Image newImage = getImage();
        if (newImage != null) {
            Element elem = getElement();
            AttributeSet attr = elem.getAttributes();
            newWidth = getIntAttr(HTML$Attribute.WIDTH, -1);
            if (newWidth > 0) {
                newState |= WIDTH_FLAG;
            }
            newHeight = getIntAttr(HTML$Attribute.HEIGHT, -1);
            if (newHeight > 0) {
                newState |= HEIGHT_FLAG;
            }
            if (newWidth <= 0) {
                newWidth = newImage.getWidth(imageObserver);
                if (newWidth <= 0) {
                    newWidth = DEFAULT_WIDTH;
                }
            }
            if (newHeight <= 0) {
                newHeight = newImage.getHeight(imageObserver);
                if (newHeight <= 0) {
                    newHeight = DEFAULT_HEIGHT;
                }
            }
            if ((newState & (WIDTH_FLAG | HEIGHT_FLAG)) != 0) {
                Toolkit.getDefaultToolkit().prepareImage(newImage, newWidth, newHeight, imageObserver);
            } else {
                Toolkit.getDefaultToolkit().prepareImage(newImage, -1, -1, imageObserver);
            }
            boolean createText = false;
            synchronized (this) {
                if (image != null) {
                    if ((newState & WIDTH_FLAG) == WIDTH_FLAG || width == 0) {
                        width = newWidth;
                    }
                    if ((newState & HEIGHT_FLAG) == HEIGHT_FLAG || height == 0) {
                        height = newHeight;
                    }
                } else {
                    createText = true;
                    if ((newState & WIDTH_FLAG) == WIDTH_FLAG) {
                        width = newWidth;
                    }
                    if ((newState & HEIGHT_FLAG) == HEIGHT_FLAG) {
                        height = newHeight;
                    }
                }
                state = state | newState;
                state = (state | LOADING_FLAG) ^ LOADING_FLAG;
            }
            if (createText) {
                updateAltTextView();
            }
        } else {
            width = height = DEFAULT_HEIGHT;
            updateAltTextView();
        }
    }
    
    private void updateAltTextView() {
        String text = getAltText();
        if (text != null) {
            ImageView$ImageLabelView newView;
            newView = new ImageView$ImageLabelView(this, getElement(), text);
            synchronized (this) {
                altView = newView;
            }
        }
    }
    
    private View getAltView() {
        View view;
        synchronized (this) {
            view = altView;
        }
        if (view != null && view.getParent() == null) {
            view.setParent(getParent());
        }
        return view;
    }
    
    private void safePreferenceChanged() {
        if (SwingUtilities.isEventDispatchThread()) {
            Document doc = getDocument();
            if (doc instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)doc).readLock();
            }
            preferenceChanged(null, true, true);
            if (doc instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)doc).readUnlock();
            }
        } else {
            SwingUtilities.invokeLater(new ImageView$1(this));
        }
    }
    {
    }
    {
    }
}
