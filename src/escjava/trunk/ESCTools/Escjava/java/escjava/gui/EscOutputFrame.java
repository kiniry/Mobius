package escjava.gui;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;

public class EscOutputFrame extends JFrame {
    public EscOutputFrame(String title, String text) {
	textArea = new JTextArea(text);
	textArea.setFont(new Font("Monospaced",Font.PLAIN,textArea.getFont().getSize()));
	textArea.setColumns(50);
	textArea.setEditable(false);
	textArea.setLineWrap(true);
	textArea.addMouseListener( new MouseInputAdapter() {
	    public void mouseClicked(MouseEvent e) {
		JTextArea textArea = (JTextArea)e.getSource();
		//if (e.getClickCount() != 3) return;
		try {
		    int p = textArea.getCaretPosition();
		    int line = textArea.getLineOfOffset(p);
		    textArea.setSelectionStart(textArea.getLineStartOffset(line));
		    textArea.setSelectionEnd(textArea.getLineEndOffset(line));
		    String s = textArea.getSelectedText();
		    try {
			GUI.windowTasks.addTask(s);
		    } catch (Exception ee) {
			return;
		    }
		} catch (Exception ee) {}
	    }
	});
	JScrollPane scroll = new JScrollPane(textArea);
	scroll.setPreferredSize(new Dimension(400,300));
	getContentPane().add(scroll, BorderLayout.CENTER);
	setLocation(500,100);
	setTitle(title);
	pack();
	showit();
    }
    public void showit() {
	EventQueue.invokeLater(new FrameShower(this));
    }
    private JTextArea textArea;
    public void appendText(String s) {
	textArea.append(s);
	showit();
    }
    public void setText(String s) {
	textArea.setText(s);
	showit();
    }
}
