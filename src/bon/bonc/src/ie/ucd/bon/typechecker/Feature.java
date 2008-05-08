/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.parser.SourceLocation;

import java.util.HashSet;
import java.util.Set;

public class Feature {

  private final SourceLocation loc;
  private final Set<String> exports;
  private boolean pub;
  private boolean priv;
  private final String className;
  
  public Feature(SourceLocation loc, String className) {
    this.loc = loc;
    this.className = className;
    
    exports = new HashSet<String>();
    pub = true;
    priv = false;
  }
  
  public void addExport(String e) {
    exports.add(e);
    pub = false;
  }
  
  public boolean containsExport(String e) {
    return exports.contains(e);
  }
  
  public void setPrivate() {
    pub = false;
    priv = true;
  }

  public boolean isPrivate() {
    return priv;
  }

  public boolean isVisible(String className) {
    return (pub && !priv) ? true : exports.contains(className);
  }

  public String getClassName() {
    return className;
  }

  public SourceLocation getSourceLocation() {
    return loc;
  }
  
  
  
  
}
