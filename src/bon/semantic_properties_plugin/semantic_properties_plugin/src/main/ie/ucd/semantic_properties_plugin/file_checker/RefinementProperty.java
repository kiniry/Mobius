package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Set;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;

/**Stores a refinement property from one level to another 
 * 
 * @author eo
 *
 */
public class RefinementProperty {
	
	private static LinkedHashMap<String,String> sConversions;
	private static LinkedHashMap<String, Transitions> oConversions;
	private static int sourceLevel;
	private static int destinationLevel;
	private static String propertyName;
	
	/**Constructs Refinement Property from input String. 
	 * 
	 * @param name of input file to parse
	 * @throws FileNotFoundException 
	 */
	public RefinementProperty(String input) {
		
		Yaml yaml = new Yaml(new Loader(new RefinementConstructor()), new Dumper(
				new RefinementRepresenter(), new DumperOptions()),
				new RefinementResolver());
		FileInputStream io=null;

		try{
			io= new FileInputStream(input);
		}
		catch(Exception e){
			System.out.println("invalid string for refinment prop");
		}
		Object ob =yaml.load(io);
		parse(ob);
	}
	/**Constructs Refinement Property from input file. 
	 * 
	 * @param input file to parse
	 * @throws FileNotFoundException 
	 */
	public RefinementProperty(File input) {
		
		Yaml yaml = new Yaml(new Loader(new RefinementConstructor()), new Dumper(
				new RefinementRepresenter(), new DumperOptions()),
				new RefinementResolver());
		FileInputStream io=null;

		try{
			io= new FileInputStream(input);
		}
		catch(Exception e){
			System.out.println("no file for refinement prop");
		}
		Object ob =yaml.load(io);
		parse(ob);
	}
	/**parse object for values of Refinement Property.
	 * 
	 * @param currentOb Object to parse.
	 */
	private void parse(Object currentOb){
		/**Entry case
		 * <p>We assume key is string.Possibly fix this later. </p>
		 */
		if(currentOb instanceof Entry<?,?>){
			Entry<Object,Object> ent=(Entry<Object,Object>) currentOb;
			
			
			
			/*check  for key relation(int,int).
			 * 
			 */
			
			Pattern p=Pattern.compile("relation\\((\\d+),(\\d+)\\)");
			Matcher m=p.matcher((String)ent.getKey());
			/**If it matches set source and destination levels. 
			 */
			if(m.matches()){
				sourceLevel=Integer.parseInt(m.group(1));
				destinationLevel=Integer.parseInt(m.group(2));
				
			}
			/**Check for property name.
			 * 
			 */
			if(ent.getKey().equals("property")){
				propertyName =(String) ent.getValue();
			}
			
			/**If value is string  add entry to sConversion .
			 * 
			 */
			else if(ent.getValue() instanceof String){
				if(sConversions==null)
					sConversions= new LinkedHashMap<String,String>();
				sConversions.put((String)ent.getKey(), (String)ent.getValue());
			}
			/**If value is Transitions add entry to oConversions
			 * 
			 */
			else if(ent.getValue() instanceof Transitions){
				if(oConversions==null)
					oConversions = new LinkedHashMap<String,Transitions>();
				oConversions.put((String)ent.getKey(), (Transitions)ent.getValue());
			}
			/**Any other object as key should be parsed.
			 * 
			 */
			else{
				parse(ent.getValue());
			}
		}
		/**Map case.
		 * 
		 */
		else if(currentOb instanceof LinkedHashMap<?,?>){
			/**Cast to map and loop through the values.
			 * 
			 */
			LinkedHashMap<Object,Object> map = (LinkedHashMap<Object,Object>)currentOb;
			Set<Entry<Object, Object>> entries = map.entrySet();
			for(Entry<Object, Object> entry:entries ){
				parse(entry);
			}
		}
		/**List case.
		 * 
		 */
		else if(currentOb instanceof ArrayList<?>){
			/**loop through list and parse each object. 
			 * 
			 */
			for(Object val: (ArrayList<Object>)currentOb){
				parse(val);
			}
		}
		else{
			System.out.println("unexpected object "+
					currentOb.toString()+
					" in RefinementProperty Parse() method");
		}
		
	}
	/**Check Validity Of RefinementProp.
	 * <p> Basic test to check that all variables are not null</p>
	 */
	static boolean isValid(){
		if(propertyName==null ||oConversions==null || sConversions==null){
			return false;
		}
		return true;		
	}
	
	/**Check if Property match p1 refines to p2.
	 * @param p1 source property match to check.
	 * @param p2 destination property to check.
 	 * @return
	 */
	public boolean isValidRefinement(PropertyMatch p1, PropertyMatch p2){
		
		return true;	
		
	}
	/**Refine p1 based on rules in this Refinement Property
	 * 
	 * @param p1 Source Property Match.
	 * @return
	 */
	public PropertyMatch refine(PropertyMatch p1){
		return p1;
		
	}
	/**Getters.
	 * 
	 */
	
	/**
	 * @return the sConversions
	 */
	public LinkedHashMap<String, String> getSConversions() {
		return sConversions;
	}
	/**
	 * @return the oConversions
	 */
	public LinkedHashMap<String, Transitions> getOConversions() {
		return oConversions;
	}
	/**
	 * @return the sourceLevel
	 */
	public int getSourceLevel() {
		return sourceLevel;
	}
	/**
	 * @return the destinationLevel
	 */
	public int getDestinationLevel() {
		return destinationLevel;
	}

}
