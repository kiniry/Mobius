/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser;

import org.antlr.runtime.tree.TreeNodeStream;
import org.antlr.runtime.tree.TreeParser;
import org.antlr.stringtemplate.StringTemplateGroup;

public abstract class AbstractBONSTWalker extends TreeParser {

  public AbstractBONSTWalker(TreeNodeStream input) {
    super(input);
  }

  public void initialise(TreeNodeStream input, StringTemplateGroup templateLib) {
    this.reset();
    this.setTreeNodeStream(input);
    this.setTemplateLib(templateLib);
  }
  
  public abstract void setTemplateLib(StringTemplateGroup templateLib);
  
}
