/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.graph.display;

import ie.ucd.bon.graph.Grapher;
import ie.ucd.bon.parser.tracker.ParsingTracker;

import java.io.ByteArrayInputStream;
import java.io.InputStream;

import javax.swing.JComponent;
import javax.swing.JFrame;

import prefuse.util.ui.UILib;


public class PrefuseGraphDisplay {

  public enum GraphingOption { ICG, IIG, NONE };
  
  public static GraphingOption getGraphingOption(final String optionString) {   
    if (optionString.equalsIgnoreCase("icg")) {
      return GraphingOption.ICG;
    } else if (optionString.equalsIgnoreCase("iig")) {
      return GraphingOption.IIG;
    } else {
      return GraphingOption.NONE;
    }    
  }
  
  public static void displayGraph(final String optionString, ParsingTracker tracker) {
    GraphingOption type = getGraphingOption(optionString);
    
    switch (type) {
    case ICG:
      displayICGGraph(tracker);
      break;
    case IIG:
      displayIIGGraph(tracker);
      break;
    case NONE:
      System.out.println("Unknown graphing type \"" + optionString + "\"");
      break;
    }
  }
  
  public static void displayICGGraph(final ParsingTracker tracker) {
    String xmlGraph = Grapher.graphPrefuseInformalClusterContainment(tracker);
    InputStream is = new ByteArrayInputStream(xmlGraph.getBytes());
    
    UILib.setPlatformLookAndFeel();
    JComponent treeview = TreeView.demo(is, "name");
    
    JFrame frame = new JFrame("b o n c  |  c l u s t e r  v i e w");
    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    frame.setContentPane(treeview);
    frame.pack();
    frame.setVisible(true);
  }
  
  public static void displayIIGGraph(final ParsingTracker tracker) {
    String xmlGraph = Grapher.graphPrefuseInformalInheritance(tracker);
    InputStream is = new ByteArrayInputStream(xmlGraph.getBytes());
    
    UILib.setPlatformLookAndFeel();
    JComponent treeview = TreeView.demo(is, "name");
    
    JFrame frame = new JFrame("b o n c  |  c l u s t e r  v i e w");
    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    frame.setContentPane(treeview);
    frame.pack();
    frame.setVisible(true);
  }
  
}
