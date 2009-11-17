package javax.swing;

import java.awt.*;
import java.awt.image.*;
import java.net.URL;
import java.io.Serializable;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import javax.accessibility.*;

public class ImageIcon implements Icon, Serializable, Accessible {
    private transient String filename;
    private transient URL location;
    transient Image image;
    transient int loadStatus = 0;
    ImageObserver imageObserver;
    String description = null;
    protected static final Component component = new ImageIcon$1();
    protected static final MediaTracker tracker = new MediaTracker(component);
    private static int mediaTrackerID;
    int width = -1;
    int height = -1;
    
    public ImageIcon(String filename, String description) {
        
        image = Toolkit.getDefaultToolkit().getImage(filename);
        if (image == null) {
            return;
        }
        this.filename = filename;
        this.description = description;
        loadImage(image);
    }
    
    public ImageIcon(String filename) {
        this(filename, filename);
    }
    
    public ImageIcon(URL location, String description) {
        
        image = Toolkit.getDefaultToolkit().getImage(location);
        if (image == null) {
            return;
        }
        this.location = location;
        this.description = description;
        loadImage(image);
    }
    
    public ImageIcon(URL location) {
        this(location, location.toExternalForm());
    }
    
    public ImageIcon(Image image, String description) {
        this(image);
        this.description = description;
    }
    
    public ImageIcon(Image image) {
        
        this.image = image;
        Object o = image.getProperty("comment", imageObserver);
        if (o instanceof String) {
            description = (String)(String)o;
        }
        loadImage(image);
    }
    
    public ImageIcon(byte[] imageData, String description) {
        
        this.image = Toolkit.getDefaultToolkit().createImage(imageData);
        if (image == null) {
            return;
        }
        this.description = description;
        loadImage(image);
    }
    
    public ImageIcon(byte[] imageData) {
        
        this.image = Toolkit.getDefaultToolkit().createImage(imageData);
        if (image == null) {
            return;
        }
        Object o = image.getProperty("comment", imageObserver);
        if (o instanceof String) {
            description = (String)(String)o;
        }
        loadImage(image);
    }
    
    public ImageIcon() {
        
    }
    
    protected void loadImage(Image image) {
        synchronized (tracker) {
            int id = getNextID();
            tracker.addImage(image, id);
            try {
                tracker.waitForID(id, 0);
            } catch (InterruptedException e) {
                System.out.println("INTERRUPTED while loading Image");
            }
            loadStatus = tracker.statusID(id, false);
            tracker.removeImage(image, id);
            width = image.getWidth(imageObserver);
            height = image.getHeight(imageObserver);
        }
    }
    
    private int getNextID() {
        synchronized (tracker) {
            return ++mediaTrackerID;
        }
    }
    
    public int getImageLoadStatus() {
        return loadStatus;
    }
    
    public Image getImage() {
        return image;
    }
    
    public void setImage(Image image) {
        this.image = image;
        loadImage(image);
    }
    
    public String getDescription() {
        return description;
    }
    
    public void setDescription(String description) {
        this.description = description;
    }
    
    public synchronized void paintIcon(Component c, Graphics g, int x, int y) {
        if (imageObserver == null) {
            g.drawImage(image, x, y, c);
        } else {
            g.drawImage(image, x, y, imageObserver);
        }
    }
    
    public int getIconWidth() {
        return width;
    }
    
    public int getIconHeight() {
        return height;
    }
    
    public void setImageObserver(ImageObserver observer) {
        imageObserver = observer;
    }
    
    public ImageObserver getImageObserver() {
        return imageObserver;
    }
    
    public String toString() {
        if (description != null) {
            return description;
        }
        return super.toString();
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        int w = s.readInt();
        int h = s.readInt();
        int[] pixels = (int[])((int[])s.readObject());
        if (pixels != null) {
            Toolkit tk = Toolkit.getDefaultToolkit();
            ColorModel cm = ColorModel.getRGBdefault();
            image = tk.createImage(new MemoryImageSource(w, h, cm, pixels, 0, w));
            loadImage(image);
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        int w = getIconWidth();
        int h = getIconHeight();
        int[] pixels = image != null ? new int[w * h] : null;
        if (image != null) {
            try {
                PixelGrabber pg = new PixelGrabber(image, 0, 0, w, h, pixels, 0, w);
                pg.grabPixels();
                if ((pg.getStatus() & ImageObserver.ABORT) != 0) {
                    throw new IOException("failed to load image contents");
                }
            } catch (InterruptedException e) {
                throw new IOException("image load interrupted");
            }
        }
        s.writeInt(w);
        s.writeInt(h);
        s.writeObject(pixels);
    }
    private ImageIcon$AccessibleImageIcon accessibleContext = null;
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new ImageIcon$AccessibleImageIcon(this);
        }
        return accessibleContext;
    }
    {
    }
}
