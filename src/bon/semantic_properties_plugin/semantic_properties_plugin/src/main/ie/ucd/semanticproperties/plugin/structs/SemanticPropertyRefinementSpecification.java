package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.api.LevelId;
import ie.ucd.semanticproperties.plugin.api.ScopeId;
import ie.ucd.semanticproperties.plugin.api.SemanticPropertyInstance;
import ie.ucd.semanticproperties.plugin.customobjects.Keyword;
import ie.ucd.semanticproperties.plugin.customobjects.MyDescription;
import ie.ucd.semanticproperties.plugin.customobjects.MyExpression;
import ie.ucd.semanticproperties.plugin.customobjects.MyFloat;
import ie.ucd.semanticproperties.plugin.customobjects.MyInt;
import ie.ucd.semanticproperties.plugin.customobjects.MyNumberObject;
import ie.ucd.semanticproperties.plugin.customobjects.MyObject;
import ie.ucd.semanticproperties.plugin.customobjects.MyObjectKind;
import ie.ucd.semanticproperties.plugin.customobjects.MyString;
import ie.ucd.semanticproperties.plugin.customobjects.MyStringObject;
import ie.ucd.semanticproperties.plugin.customobjects.Nat;
import ie.ucd.semanticproperties.plugin.exceptions.IncompatibleSemanticPropertyInstancesException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidRefinementException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidRefinementSpecificationException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownLevelException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownVariableIdentifierException;
import ie.ucd.semanticproperties.plugin.yaml.CustomConstructor;
import ie.ucd.semanticproperties.plugin.yaml.CustomRepresenter;
import ie.ucd.semanticproperties.plugin.yaml.CustomResolver;
import ie.ucd.semanticproperties.plugin.yaml.RefinementConstructor;
import ie.ucd.semanticproperties.plugin.yaml.RefinementRepresenter;
import ie.ucd.semanticproperties.plugin.yaml.RefinementResolver;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;



/**
 * Stores a refinement property from one level to another.
 * @author eo
 *
 */
public class SemanticPropertyRefinementSpecification {

  private LinkedHashMap<String,String> sConversions;
  private LinkedHashMap<String, Transitions> oConversions;
  private LevelId sourceLevel;
  private LevelId destinationLevel;
  private String propertyName;


  /**Constructor for  Object.
   * @param input object with property in it.
   * @throws UnknownLevelException
   * @throws InvalidRefinementSpecificationException
   */
  public SemanticPropertyRefinementSpecification(Object input) throws UnknownLevelException, InvalidRefinementSpecificationException {
    parse(input);

  }
  /**
   * Constructs Refinement LevelRepresenation from input String.
   * @param input string in yaml form to parse.
   * @throws UnknownLevelException
   * @throws FileNotFoundException
   */
  public SemanticPropertyRefinementSpecification(final String input) throws UnknownLevelException , InvalidRefinementSpecificationException{

    Yaml yaml = new Yaml(new Loader(new RefinementConstructor()), new Dumper(new RefinementRepresenter(), new DumperOptions()), new RefinementResolver());
    Object ob = yaml.load(input);
    parse(ob);
  }
  /**Constructs Refinement LevelRepresenation from input file.
   * 
   * @param input file to parse
   * @throws UnknownLevelException
   * @throws FileNotFoundException
   * @throws FileNotFoundException
   */
  public SemanticPropertyRefinementSpecification(final File input) throws UnknownLevelException, FileNotFoundException, InvalidRefinementSpecificationException {

    Yaml yaml = new Yaml(new Loader(new RefinementConstructor()), new Dumper(new RefinementRepresenter(), new DumperOptions()), new RefinementResolver());
    FileInputStream io = new FileInputStream(input);
    Object ob = yaml.load(io);
    parse(ob);
  }
  /**parse object for values of Refinement LevelRepresenation.
   * 
   * @param currentOb Object to parse.
   * @throws UnknownLevelException
   */
  private void parse(final Object currentOb) throws UnknownLevelException, InvalidRefinementSpecificationException {
    /**Entry case
     * <p>We assume key is string.Possibly fix this later. </p>
     */
    if (currentOb instanceof Entry< ? , ? >) {
      Entry<Object, Object> ent = (Entry<Object, Object>) currentOb;
      
      /**
       * do key
       */
      
      /**check  for key relation(int,int).
       * 
       */

      Pattern p = Pattern.compile("relation\\((\\w+),(\\w+)\\)");
      Matcher m = p.matcher((String) ent.getKey());
      /**If it matches set source and destination levels. 
       */
      if (m.matches()) {
        sourceLevel = LevelId.levelIdFor(m.group(1));
        destinationLevel = LevelId.levelIdFor(m.group(2));

      }
      /**Check for property name.
       * 
       */
      if (ent.getKey().equals("property")) {
        propertyName = (String) ent.getValue();
        if (sConversions == null) {
          sConversions = new LinkedHashMap<String, String>();
        }
        sConversions.put(propertyName, propertyName);
      }

      /**If value is string  add entry to sConversion .
       * 
       */

      else if (ent.getValue() instanceof String) {
        if (sConversions == null) {
          sConversions = new LinkedHashMap<String, String>();
        }
        sConversions.put((String) ent.getKey(),
            (String) ent.getValue());
      }
      /**If value is Transitions add entry to oConversions
       * 
       */
      else if (ent.getValue() instanceof Transitions) {
        if (oConversions == null) {
          oConversions = new LinkedHashMap<String, Transitions>();
        }
        oConversions.put((String) ent.getKey(), 
            (Transitions) ent.getValue());
      }
      /**Any other object as key should be parsed.
       * 
       */
      else {
        parse(ent.getValue());
      }
    }
    /**Map case.
     * 
     */
    else if (currentOb instanceof LinkedHashMap< ? , ? >) {
      /**Cast to map and loop through the values.
       * 
       */
      LinkedHashMap<Object, Object> map = 
        (LinkedHashMap<Object, Object>) currentOb;
      Set<Entry<Object, Object>> entries = map.entrySet();
      for (Entry<Object, Object> entry : entries ) {
        parse(entry);
      }
    }
    /**List case.
     * 
     */
    else if (currentOb instanceof ArrayList< ? >) {
      /**loop through list and parse each object. 
       * 
       */
      for (Object val : (ArrayList<Object>) currentOb){
        parse(val);
      }
    }
    else{
      System.out.println("unexpected object "
          + currentOb.toString()
          + " in Refinement Parse() method");
      throw new InvalidRefinementSpecificationException();
    }

  }


  /**Check if LevelRepresenation match p1 refines to p2.
   * @param p1 source property match to check.
   * @param p2 destination property to check.
   * @return true if p1 refines to p2.
   * @throws UnknownVariableIdentifierException
   * @throws IncompatibleSemanticPropertyInstancesException
   * @throws InvalidRefinementException
   */
  public final boolean isValidRefinement(final SemanticPropertyInstance p1, final SemanticPropertyInstance p2,SemanticPropertyLevelSpecification spl1, SemanticPropertyLevelSpecification spl2) throws  IncompatibleSemanticPropertyInstancesException, InvalidRefinementException{
    /**
     * Check if p1,p2,spl1,spl2 don't equal null
     */
    if(p1==null|p2==null|spl1==null|spl2==null){
      throw new InvalidRefinementException();
    }
    /**
     * Check that p1 and p2 are right levels for this refinement.
     */
    if(!(sourceLevel == p1.getLevel() || destinationLevel == p2.getLevel())) {
      throw new IncompatibleSemanticPropertyInstancesException();
    }
    /**
     * Check that all captur strings are refined
     */
//    for(String cur : p1.getStringMap()) {
//      if(sConversions.containsKey(cur)){
//        String keyToCompare = sConversions.get(cur);
//        if(!(p2.getStringMap().contains(keyToCompare))){
//          throw new InvalidRefinementException();
//        }
//      } else {
//        throw new InvalidRefinementException();
//      }
//    }
    /**
     * Check all the capturing groups are refined.
     */
    Iterator<String> it = oConversions.keySet().iterator();
    while (it.hasNext()) {
      try {
        String presKey = (String) it.next();
        /**
         * Set type of objects from propertyLevelSpec
         */
        MyObject ob1 = (MyObject)spl1.getReg().getGroupObj().get(presKey);
        MyObject ob2 = (MyObject)spl2.getReg().getGroupObj().get(presKey);
        /**
         * Set value from instances.
         */
        ob1.setValue(p1.getVariable(presKey));
        ob2.setValue(p2.getVariable(presKey));

        //check if p1 is a valid conversion for ob1. remove later
        if (ob1 == null) {
          return false;
        }
        //check the type of conversion
        Transitions tran = oConversions.get(presKey);
        //for string conversions
        if ((ob1 instanceof MyStringObject) && (ob2 instanceof MyStringObject)){
          String a = (String) ob1.getValue();
          String b = (String) ob2.getValue();
          //deal with each conversion appropriately
          if (tran.equals(Transitions.prefix)) {
            if (!b.startsWith(a)) {
              throw new InvalidRefinementException();
            }
          } else if (tran.equals(Transitions.substring)) {
            if (!b.contains(a)) {
              throw new InvalidRefinementException();
            }
          } else if (tran.equals(Transitions.suffix)) {
            if (!b.endsWith(a)) {
              throw new InvalidRefinementException();
            }
          } else if (tran.equals(Transitions.equals)) {
            if (!b.equals(a)) {
              throw new InvalidRefinementException();
            }
          }
        } else if ((ob1 instanceof MyNumberObject) && (ob2 instanceof MyNumberObject)){
          Float a;
          Float b;
          if(ob1 instanceof MyInt || ob1 instanceof Nat){
            a = ((Number)ob1.getValue()).floatValue();
            b = ((Number)ob2.getValue()).floatValue();
          } else{
             a = (Float)ob1.getValue();
             b = (Float)ob2.getValue();
          }
          /**
           * Deal with transitions
           */
          if (tran.equals(Transitions.LessThan)) {
            if (!(a<b)) {
              throw new InvalidRefinementException();
            }
          } else if (tran.equals(Transitions.LessThanOrEquals)) {
            if (!(a<=b)) {
              throw new InvalidRefinementException();
            }
          } else if (tran.equals(Transitions.greaterThan)) {
            if (!(a>b)) {
              throw new InvalidRefinementException();
            }
          } else if (tran.equals(Transitions.greaterThanOrEquals)) {
            if (!(a>=b)) {
              throw new InvalidRefinementException();
            }
          }
          /**
           * other transitions ... equal are not 
           */
        } else{
          if (tran.equals(Transitions.equals)) {
            if(!(ob1.getValue().equals(ob2.getValue()))){
              throw new InvalidRefinementException();
            }
          }
          
        }
      } catch(UnknownVariableIdentifierException e){
        // this just means that not all options for this level were filled in this instance
      }
      
      
      //check strings
      Iterator<String> it2 = sConversions.keySet().iterator();
      while (it2.hasNext()) {
        
        
          
          String presKey = (String) it2.next();
          
          Object t1 = spl1.getReg().getGroupObj().get(presKey);
          Object t2 = spl2.getReg().getGroupObj().get(sConversions.get(presKey));
          
          
          if(t1 instanceof Keyword && t2 instanceof Keyword){
             Keyword k1= (Keyword) t1;
             Keyword k2 = (Keyword) t2;
             try{
               k1 = new Keyword(k1.getKeyword(),(String)p1.getVariable(presKey));
               k2  = new Keyword(k2.getKeyword(),(String)p2.getVariable(sConversions.get(presKey)));
             } catch(UnknownVariableIdentifierException e) {
            
             }
             
             if(!(sConversions.get(k1.getValue()).equals(k2.getValue()))){
               throw new InvalidRefinementException();
             }
          }
      }
    }
    return true;
  }


  /**Refine p1 based on rules in this Refinement LevelRepresenation.
   * 
   * @param p1 Source LevelRepresenation Match.
   * @return The refinement of p1 using this refinement property.
   * @param level the level to refine to.
   * @param propLev 
   * @throws IncompatibleSemanticPropertyInstancesException 
   * @throws InvalidRefinementException 
   */
  public final SemanticPropertyInstance refine(final SemanticPropertyInstance  p1, LevelId level, SemanticPropertyLevelSpecification spl1) throws IncompatibleSemanticPropertyInstancesException, InvalidRefinementException {
    /**
     * Check that p1 and p2 are right levels for this refinement.
     */
    if(!(sourceLevel == p1.getLevel()) || !(destinationLevel == level)) {
      throw new IncompatibleSemanticPropertyInstancesException();
    }
    /**
     * Variables that will make up refined SemanticPropertyInstance.
     */
    HashMap<String,Object> newCaptured = new HashMap <String, Object>();
//   LinkedList<String> newString = new LinkedList <String>();
    /**
     * refine all the capturing groups.
     */
    Iterator<String> it = oConversions.keySet().iterator();
    while (it.hasNext()) {
      try {
        String presKey = (String) it.next();
        /**
         * Set type of objects from propertyLevelSpec
         */
        MyObject ob1 = (MyObject)spl1.getReg().getGroupObj().get(presKey);

        /**
         * Set value from instance.
         */
        ob1.setValue(p1.getVariable(presKey));

        if (ob1 == null) {
          throw new IncompatibleSemanticPropertyInstancesException();
        }
        //check the type of conversion
        Transitions tran = oConversions.get(presKey);
        //for string conversions
        if ((ob1 instanceof MyStringObject)){
          String a = (String) ob1.getValue();
          String pre ="";
          String post="";
          //deal with each conversion appropriately
          if (tran.equals(Transitions.prefix)) {
            post = "";
          } else if (tran.equals(Transitions.substring)) {
            pre = "";
            post = "";
          } else if (tran.equals(Transitions.suffix)) {
            pre = "";
          } else if (tran.equals(Transitions.equals)) {

          }
          MyObject temp = new MyObject();
          temp.setId(ob1.getId());
          temp.setValue((pre + ob1.getValue() + post));
          newCaptured.put(presKey, temp.getValue());
        } else if ((ob1 instanceof MyNumberObject)){
          /**
           * Convert all to float 
           */
          float a;

          if(ob1 instanceof MyInt || ob1 instanceof Nat){
            a = ((Number)ob1.getValue()).floatValue();
          }
          else{
             a = (Float)ob1.getValue();
          }
          float newFloat = a;
          //deal with each conversion appropriately
          if (tran.equals(Transitions.LessThan)) {
            newFloat = a + new Float(1.0);
          } else if (tran.equals(Transitions.LessThanOrEquals)) {
            newFloat = a + new Float(1.0);
          } else if (tran.equals(Transitions.greaterThan)) {
            newFloat = a - new Float(1.0);
          } else if (tran.equals(Transitions.greaterThanOrEquals)) {
            newFloat = a - new Float(1.0);
          }

          MyObject temp =new MyObject();
          temp.setId(ob1.getId());
          temp.setValue(newFloat);
          newCaptured.put(presKey, temp.getValue());
          /**
           * rest of object kinds
           */
        } else{
          if (tran.equals(Transitions.equals)) {
            newCaptured.put(presKey, ob1.getValue());
          }
          
        }
      } catch(UnknownVariableIdentifierException e) {
        // this just means that not all options for this level were filled in this instance
      }

    }

    /**
     * Refine all strings.
     */
    //check strings
    
    Iterator<String> it2 = sConversions.keySet().iterator();
    while (it2.hasNext()) {
      
      
        
        String presKey = (String) it2.next();
        
        Object t1 = spl1.getReg().getGroupObj().get(presKey);
        
        
        
        if(t1 instanceof Keyword){
           Keyword k1= (Keyword) t1;

           try{
             k1 = new Keyword(k1.getKeyword(),(String)p1.getVariable(presKey));
             
             Keyword newk = new Keyword(sConversions.get(k1.getKeyword()),sConversions.get(k1.getValue()));
             newCaptured.put(newk.getKeyword(), newk.getValue());

           } catch(UnknownVariableIdentifierException e) {
          
           }
        
        }
    }

    return new SemanticPropertyInstance(p1.getPropertyType(),level,p1.getScope(),newCaptured,spl1.getPrettyPrint());
  }
  /**
   * Getters.
   */

  /**
   * @return the sConversions.
   */
  public final LinkedHashMap<String, String> getSConversions() {
    return sConversions;
  }
  /**
   * @return the oConversions
   */
  public final LinkedHashMap<String, Transitions> getOConversions() {
    return oConversions;
  }
  /**
   * @return the sourceLevel
   */
  public final LevelId getSourceLevel() {
    return sourceLevel;
  }
  /**
   * @return the destinationLevel
   */
  public final LevelId getDestinationLevel() {
    return destinationLevel;
  }

}
