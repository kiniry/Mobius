/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.graph.display;

import ie.ucd.bon.clinterface.BONcOptionsInterface;
import ie.ucd.bon.graph.Grapher;
import ie.ucd.bon.parser.tracker.ParsingTracker;

import java.io.ByteArrayInputStream;
import java.io.InputStream;

import javax.swing.JComponent;
import javax.swing.JFrame;

import prefuse.util.ui.UILib;


public class PrefuseGraphDisplay {

  public static void displayGraph(final BONcOptionsInterface.Graph graphOption, ParsingTracker tracker) {

    switch (graphOption) {
    case ICG:
      displayICGGraph(tracker);
      break;
    case IIG:
      displayIIGGraph(tracker);
      break;
    }
  }

  public static void displayICGGraph(final ParsingTracker tracker) {
    //TODO fix
//    String xmlGraph = Grapher.graphPrefuseInformalClusterContainment(tracker);
//    InputStream is = new ByteArrayInputStream(xmlGraph.getBytes());
//
//    UILib.setPlatformLookAndFeel();
//    JComponent treeview = TreeView.demo(is, "name");
//
//    JFrame frame = new JFrame("b o n c  |  c l u s t e r  v i e w");
//    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
//    frame.setContentPane(treeview);
//    frame.pack();
//    frame.setVisible(true);
  }

  public static void displayIIGGraph(final ParsingTracker tracker) {
  //TODO fix
//    String xmlGraph = Grapher.graphPrefuseInformalInheritance(tracker);
//    InputStream is = new ByteArrayInputStream(xmlGraph.getBytes());
//
//    UILib.setPlatformLookAndFeel();
//    JComponent treeview = TreeView.demo(is, "name");
//
//    JFrame frame = new JFrame("b o n c  |  c l u s t e r  v i e w");
//    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
//    frame.setContentPane(treeview);
//    frame.pack();
//    frame.setVisible(true);
  }

}
