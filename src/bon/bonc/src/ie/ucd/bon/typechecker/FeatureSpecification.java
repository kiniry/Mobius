/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;


public class FeatureSpecification {

  private final Feature feature;
  private boolean deferred;
  private boolean effective;
  private boolean redefined;
  private Type type;
  private Renaming renaming;
  private final Map<String,FeatureArgument> argsMap;
  private final Collection<FeatureSpecificationInstance> instances;
  
  private String precondition;
  private String postcondition;
  
  public FeatureSpecification(Feature feature) {
    this.feature = feature;
    
    deferred = false;
    effective = false;
    redefined = false;
    type = null;
    renaming = null;
    
    argsMap = new HashMap<String,FeatureArgument>();
    instances = new Vector<FeatureSpecificationInstance>();
  }

  public void setDeferred() {
    this.deferred = true;
  }  
  
  public boolean isDeferred() {
    return deferred;
  }

  public boolean isEffective() {
    return effective;
  }

  public boolean isRedefined() {
    return redefined;
  }

  public Renaming getRenaming() {
    return renaming;
  }

  public void setEffective() {
    this.effective = true;
  }

  public void setRedefined() {
    this.redefined = true;
  }

  public void setType(Type type) {
    this.type = type;
  }  
    
  public String getPrecondition() {
    return precondition;
  }

  public void setPrecondition(String precondition) {
    this.precondition = precondition;
  }

  public String getPostcondition() {
    return postcondition;
  }

  public void setPostcondition(String postcondition) {
    this.postcondition = postcondition;
  }

  public String getClassName() {
    return feature.getClassName();
  }

  public Type getType() {
    return type;
  }

  public Map<String,FeatureArgument> getArgs() {
    return argsMap;
  }

  public void setRenaming(String className, String featureName) {
    renaming = new Renaming(className, featureName);
  }
  
  public void addArgument(String name, Type type) {
    FeatureArgument arg = new FeatureArgument(name, type);
    if (name != null) {
      argsMap.put(name, arg);
    }
  }
  
  public void addInstance(FeatureSpecificationInstance instance) {
    instances.add(instance);
  }
  
  public int getNumberOfInstances() {
    return instances.size();
  }
  
  public class Renaming {
    private final String className;
    private final String featureName;
    public Renaming(String className, String featureName) {
      this.className = className;
      this.featureName = featureName;
    }
    public String getClassName() {
      return className;
    }
    public String getFeatureName() {
      return featureName;
    }
    
  }
}
