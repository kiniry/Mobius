package escjava.gui;

import java.awt.Frame;

public class FrameShower implements Runnable {
    final Frame frame;
    public FrameShower(Frame frame) {
	this.frame = frame;
    }
    public void run() {
	frame.show();
    }
}


