/*
 * Software Engineering Tools.
 *
 * $Id: WindowOutput.jass,v 1.1.1.1 2002/12/29 12:36:17 kiniry Exp $
 *
 * Copyright (c) 1997-2001 Joseph Kiniry
 * Copyright (c) 2000-2001 KindSoftware, LLC
 * Copyright (c) 1997-1999 California Institute of Technology
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * - Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 
 * - Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 * 
 * - Neither the name of the Joseph Kiniry, KindSoftware, nor the
 * California Institute of Technology, nor the names of its contributors
 * may be used to endorse or promote products derived from this software
 * without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS ``AS
 * IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL KIND SOFTWARE OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package mobius.logging;

import java.awt.BorderLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

/**
 * <p> The primary class used to send messages to a window created by
 * the IDebug framework. </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @concurrency (GUARDED) All methods are synchronized.
 * @see Context
 * @see Debug
 *
 * @todo Can we actually provide a valid Writer for getWriter()?
 */
//@ non_null_by_default
public class WindowOutput extends AbstractDebugOutputBase
  implements DebugOutput, Cloneable
{
  // Attributes

  /** The frame used by this class. */
  private JFrame my_frame;

  /** The text area used by this class. */
  private JTextArea my_text_area;

  // Constructors

  //@ assignable my_debug;
  //@ ensures my_debug == the_debug;
  /**
   * Construct a new WindowOutput class.
   *
   * @param the_debug the Debug class associated with this WindowOutput.
   */
  public WindowOutput(final Debug the_debug)
  {
    this.my_debug = the_debug;

    // set up swing components.
    createUI();
  }

  // Inherited Methods

  /**
   * {@inheritDoc}
   */
  public synchronized void printMsg(final String the_category, final String the_message)
  {
    my_text_area.append("<" + the_category + ">: " + the_message);
  }

  /**
   * {@inheritDoc}
   */
  public synchronized void printMsg(final int the_level, final String the_message)
  {
    my_text_area.append("[" + the_level + "]: " + the_message);
  }

  /**
   * {@inheritDoc}
   */
  public synchronized void printMsg(final String the_message)
  {
    my_text_area.append(the_message);
  }

  /**
   * {@inheritDoc}
   */
  public synchronized Writer getWriter()
  {
    return null;
  }

  /**
   * {@inheritDoc}
   */
  public Object clone() throws CloneNotSupportedException
  {
    try {
      return super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage(), cnse);
    }
  }

  // Protected Methods
  // Package Methods
  // Private Methods

  /**
   * Build the user interface.  The UI consists of a JFrame containing a
   * small set of components: a text area with a scrollbar for debugging
   * messages, a "clear" button to clear the current messages, and a "save"
   * button to save the current debugging messages to a textfile.
   */
  private void createUI()
  {
    // Create the top-level container and add contents to it.
    my_frame = new JFrame("IDebug Output");

    // Create the text area to write into and a surrounding scrollpane so
    // that the user can look back at text that has scrolled by.
    my_text_area = new JTextArea(30, 80);
    my_text_area.setEditable(false);
    my_text_area.setLineWrap(true);
    my_text_area.setWrapStyleWord(true);
    final JScrollPane areaScrollPane =
      new JScrollPane(my_text_area,
                      JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
                      JScrollPane.HORIZONTAL_SCROLLBAR_ALWAYS);

    // Create the "clear" button that clears the text in textArea.
    final JButton clearButton = new JButton("Clear");
    clearButton.setToolTipText("Clear debugging log.");
    clearButton.addActionListener(new ActionListener() {
        public void actionPerformed(final ActionEvent the_event) {
          // react to clear command
          my_text_area.setText("");
        }
      });

    // Create the "save" button that lets the user save the contents of
    // textArea to a file.
    final JButton saveButton = new JButton("Save");
    saveButton.setToolTipText("Save debugging log to a file.");
    saveButton.addActionListener(new ActionListener() {
        public void actionPerformed(final ActionEvent the_event) {
          // react to save command
          final JFileChooser fileChooser = new JFileChooser();
          fileChooser.setDialogTitle("Save debug log to which file?");
          final int result = fileChooser.showSaveDialog(my_frame);
          File file = null;
          if (result == JFileChooser.APPROVE_OPTION) {
            file = fileChooser.getSelectedFile();
          }
          final String filename = file.getAbsolutePath();
          if (file.isDirectory()) {
            JOptionPane.showMessageDialog(null,
                        filename + " is not a file!",
                        "IDebug Error", JOptionPane.ERROR_MESSAGE);
            return;
          }
          if (file.exists() && !file.canWrite()) {
            JOptionPane.showMessageDialog(null,
                        filename + " is not a writable file!",
                        "IDebug Error", JOptionPane.ERROR_MESSAGE);
            return;
          }
          try {
            final FileWriter fileWriter = new FileWriter(file);
            fileWriter.write(my_text_area.getText());
            fileWriter.close();
          } catch (IOException ioe) {
            JOptionPane.showMessageDialog(null,
                  "Error while writing debug log to file " + filename,
                  "IDebug Error", JOptionPane.ERROR_MESSAGE);
          }
        }
      });

    // Create the "close" button that closes the frame.
    final JButton closeButton = new JButton("Close");
    closeButton.setToolTipText("Close debugging log window.");
    closeButton.addActionListener(new ActionListener() {
        public void actionPerformed(final ActionEvent the_event) {
          // react to close command
          final int result =
            JOptionPane.showConfirmDialog(null,
                                          "Are you sure you want to close the log window?\n" +
                                          "You cannot open it again without restarting.",
                                          "IDebug Warning", JOptionPane.YES_NO_OPTION);
          if (result == JOptionPane.YES_OPTION)
            my_frame.hide();
        }
      });

    // Create a panel into which we'll put the buttons.
    final JPanel panel = new JPanel();
    panel.setBorder(BorderFactory.createEmptyBorder(30, //top    NOPMD
                                                    30, //left   NOPMD
                                                    10, //bottom NOPMD
                                                    30) //right  NOPMD
    );
    panel.setLayout(new GridLayout(1, 2)); // NOPMD
    panel.add(clearButton);
    panel.add(saveButton);
    panel.add(closeButton);

    my_frame.getContentPane().add(areaScrollPane, BorderLayout.NORTH);
    my_frame.getContentPane().add(panel, BorderLayout.SOUTH);

    //Finish setting up the frame, and show it.
    my_frame.addWindowListener(new WindowAdapter() {
        public void windowClosing(final WindowEvent the_event) {
          // react to close event on window
        }
      });
    my_frame.pack();
    my_frame.setVisible(true);
  }

} // end of class WindowOutput

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End: */
