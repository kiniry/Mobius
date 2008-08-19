/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal;

import ie.ucd.bon.source.SourceLocation;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

public class ClassChartDefinition {

    private final String className;
    private final SourceLocation loc;
    
    private String explanation;
    
    private final Set<String> superClasses;
    
    private boolean hasClassHierarchyCycle;
    
    private final Collection<String> queries;
    private final Collection<String> commands;
    private final Collection<String> constraints;
    
    public ClassChartDefinition(String className, SourceLocation loc) {
      this.className = className;
      this.loc = loc;
      this.superClasses = new HashSet<String>();
      queries = new LinkedList<String>();
      commands = new LinkedList<String>();
      constraints = new LinkedList<String>();
    }

    public String getClassName() {
      return className;
    }

    public SourceLocation getSourceLocation() {
      return loc;
    }

    public void addSuperClass(String className) {
      superClasses.add(className);
    }
    
    public boolean hasSuperClass(String className) {
      return superClasses.contains(className);
    }

    public Collection<String> getSuperClasses() {
      return superClasses;
    }
  
    @Override
    public boolean equals(Object obj) {
      if (obj instanceof ClassChartDefinition) {
        return className.equals(((ClassChartDefinition)obj).className);
      } else {
        return false;
      }
    }

    @Override
    public int hashCode() {
      return className.hashCode();
    }

    public boolean hasClassHierarchyCycle() {
      return hasClassHierarchyCycle;
    }

    public void setHasClassHierarchyCycle() {
      this.hasClassHierarchyCycle = true;
    }

    public String getExplanation() {
      return explanation;
    }

    public void setExplanation(String explanation) {
      this.explanation = explanation;
    }

    public void addQuery(String query) {
      queries.add(query);
    }
    
    public Collection<String> getQueries() {
      return queries;
    }
    
    public void addCommand(String command) {
      commands.add(command);
    }
    
    public Collection<String> getCommands() {
      return commands;
    }
    
    public void addConstraint(String constraint) {
      constraints.add(constraint);
    }
    
    public Collection<String> getConstraints() {
      return constraints;
    }
    
    
}
