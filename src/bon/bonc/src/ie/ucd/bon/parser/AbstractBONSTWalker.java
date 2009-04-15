/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser;

import ie.ucd.bon.Printer.PrintingOption;
import ie.ucd.bon.printer.PrintingTracker;
import ie.ucd.bon.util.StringUtil;

import org.antlr.runtime.RecognizerSharedState;
import org.antlr.runtime.tree.TreeNodeStream;
import org.antlr.runtime.tree.TreeParser;
import org.antlr.stringtemplate.StringTemplateGroup;

public abstract class AbstractBONSTWalker extends TreeParser {
 
  private PrintingTracker printingTracker;
  private PrintingOption printingOption;
  
  public AbstractBONSTWalker(TreeNodeStream input, RecognizerSharedState state) {
    super(input, state);
  }

  public void initialise(TreeNodeStream input, StringTemplateGroup templateLib, PrintingTracker printingTracker, PrintingOption printingOption) {
    this.reset();
    this.setTreeNodeStream(input);
    this.setTemplateLib(templateLib);
    
    this.printingTracker = printingTracker;
    this.printingOption = printingOption;
  }
  
  public abstract void setTemplateLib(StringTemplateGroup templateLib);
  
  protected PrintingTracker getPT() {
    return printingTracker;
  }
  
  protected String stripRemovingSpeechMarksIfNecessary(String s) {
    switch (printingOption) {
    case HTML:
      return StringUtil.stripForHTML(s, false);
    default:
      return s;
    }
  }

  protected String stripIfNecessary(String s) {
    switch (printingOption) {
    case HTML:
      return StringUtil.stripForHTML(s, true);
    default:
      return s;
    }
  }
  
  protected String removeSpeechMarksIfNecessary(String s) {
    switch (printingOption) {
    case HTML:
      return s.substring(1, s.length()-1);
    default:
      return s;
    }
  }
}
