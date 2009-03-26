/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.Main;
import ie.ucd.bon.ast.BONType;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.informal.ClassChartDefinition;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

public class ClassDefinition extends ClassChartDefinition implements Comparable<ClassDefinition> {

  private boolean root;
  private boolean deferred;
  private boolean effective;
  private boolean reused;
  private boolean persistent;
  private boolean interfaced;
  private final Map<String,FormalGeneric> formalGenerics;
  private boolean hasFormalGenerics;
  private final Map<String,FeatureSpecificationInstance> features;
  private Collection<FeatureSpecificationInstance> deferredFeatures;
  
  private final Collection<String> invariants;
  
  private final TypingInformation typingInfo;
  
  public ClassDefinition(String className, SourceLocation loc, TypingInformation typingInfo) {
    super(className, loc);
    
    this.typingInfo = typingInfo;
    formalGenerics = new HashMap<String,FormalGeneric>();
    hasFormalGenerics = false;
    features = new HashMap<String,FeatureSpecificationInstance>();
   
    invariants = new LinkedList<String>();
    
    root = false;
    deferred = false;
    effective = false;
    reused = false;
    persistent = false;
    interfaced = false;
  }

  public boolean hasParentClass(BONType parent) {
    return typingInfo.getSimpleClassInheritanceGraph().getLinkedNodes(getClassName()).contains(parent.getNonGenericType());
  }
  
  public void addFormalGeneric(String name, Type type, SourceLocation loc) {
    hasFormalGenerics = true;
    formalGenerics.put(name, new FormalGeneric(name,type,loc));
  }
  
  public Collection<FormalGeneric> getFormalGenerics() {
    return formalGenerics.values();
  }
  
  public boolean hasFormalGeneric(String name) {
    return formalGenerics.containsKey(name);
  }
  
  public boolean hasFormalGenerics() {
    return hasFormalGenerics;
  }
  
  public void setRoot() {
    this.root = true;
  }

  public void setDeferred() {
    this.deferred = true;
  }

  public void setEffective() {
    this.effective = true;
  }

  public boolean isDeferred() {
    return deferred;
  }

  public boolean isEffective() {
    return effective;
  }

  public boolean isRoot() {
    return root;
  }

  public void addFeature(FeatureSpecificationInstance instance) {
    features.put(instance.getName(), instance);
  }
  
  public boolean containsFeatureByName(String name) {
    return features.containsKey(name);
  }
  
  public FeatureSpecificationInstance getFeatureByName(String name) {
    return features.get(name);
  }

  public Collection<FeatureSpecificationInstance> getFeatures() {
    return features.values();
  }

  public Set<BONType> getParentClasses() {
    return typingInfo.getClassInheritanceGraph().getLinkedNodes(getClassName());
  }
  
  public Set<String> getSimpleParentClasses() {
    return typingInfo.getSimpleClassInheritanceGraph().getLinkedNodes(getClassName());
  }
  
  public Collection<FeatureSpecificationInstance> getDeferredFeatures() {
    if (deferredFeatures == null) {
      deferredFeatures = new Vector<FeatureSpecificationInstance>();
      
      for (FeatureSpecificationInstance i : features.values()) {
        if (i.getFeatureSpec().isDeferred()) {
          deferredFeatures.add(i);
        }
      }
    }
    return deferredFeatures;
  }

  public boolean equals(Object obj) {
    return obj instanceof ClassDefinition ? getClassName().equals(((ClassDefinition)obj).getClassName()) : false;
  }

  public int hashCode() {
    return getClassName().hashCode();
  }

  @Override
  public String toString() {
    return "ClassDefinition:" + getClassName();
  }

  public int compareTo(ClassDefinition o) {
    return this.getClassName().compareTo(o.getClassName());
  }

  public Collection<String> getInvariants() {
    return invariants;
  }
  
  public void addInvariant(String invariant) {
    invariants.add(invariant);
  }

  public boolean isReused() {
    return reused;
  }

  public void setReused(boolean reused) {
    this.reused = reused;
  }

  public boolean isPersistent() {
    return persistent;
  }

  public void setPersistent(boolean persistent) {
    Main.logDebug("Setting persistent: " + persistent);
    this.persistent = persistent;
  }

  public boolean isInterfaced() {
    return interfaced;
  }

  public void setInterfaced(boolean interfaced) {
    Main.logDebug("Setting interfaced: " + interfaced);
    this.interfaced = interfaced;
  }

  @Override
  public Collection<String> getSuperClasses() {
    return getSimpleParentClasses();
  }
  
  
  
}
