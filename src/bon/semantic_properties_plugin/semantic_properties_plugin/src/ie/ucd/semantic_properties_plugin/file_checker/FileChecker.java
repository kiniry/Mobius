package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.*;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.Iterator;

import org.yaml.snakeyaml.Yaml;

public class FileChecker {

	final static String prop_Scope = "property_scope(\\s)*:(\\s)*( files | modules | features | variables | all | special )(,( files | modules | features | variables | all | special ))*";
	final static String prop_Name = "property_name(\\s)*:(\\s)*";
	// dosnt account for case where everything is surrounded by bracket
	final static String prop_Form = "(\\w*) ( (\\w)* | (<(\\w)*>) | ( \\( (\\w)* \\) )*)*";
	final static String prop_Description = "property_description(\\s)*:(\\w)*";
	static List<Property> allprops;

	// for testing purposes
	final static String regEx = ".*+";

	public static void main(String[] args) throws FileNotFoundException {
		//initialise values
		allprops= new LinkedList<Property>();
		
		//parse in yaml file
		parseFile(getInputFile());
		
		// check the validity
		System.out.println("This validity of the the property is "+checkvalidity());

	}

	private static String getInputFile() {
		System.out.println("enter file name (from resources/examples/ folder)");

		// get name of file
		BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
		String inputfile = null;

		try {
			inputfile = br.readLine();
		} catch (IOException ioe) {
			System.out.println("IO error trying to read file name!");
			System.exit(1);
		}
		return inputfile;
	}

	private static String parseFile(String inputfile) {
		InputStream input = null;
		try {
			input = new FileInputStream(new File("resources/examples/"+inputfile));
		} catch (FileNotFoundException e) {
			System.out.println("error reading from " + inputfile + " file");
			e.printStackTrace();
			System.exit(1);
		}
		Yaml yaml = new Yaml();
		Object data = yaml.loadAll(input);

		//System.out.println(data.toString());
		
		if(data instanceof LinkedHashMap<?, ?>){
			System.out.println("is linkedhashmap");
			LinkedHashMap<String,?> h;
			h = (LinkedHashMap<String,?>)data;
			System.out.println(h.toString());
		}
		else if(data instanceof Iterable){
			System.out.println("multiple properites");
			Iterator<LinkedHashMap<String,?>> i;
			//iterate through the properties and add them
			
			Iterable s=(Iterable<?>)data;
			i=s.iterator();
			System.out.println(i.toString());
			while(i.hasNext()){
				
				addProperty(i.next());
			}
			
		}
		else{
			System.out.println("not linkedHashMap or Iterator");
		}
		//String stringdump = yaml.dump(data);

		//System.out.print(stringdump);
		return "dummy";

	}

	public static boolean checkvalidity() {

		for (int i=0;i<allprops.size(); i++ ){
			Property tempProp =allprops.get(i);
			if( tempProp.checkValidity()==false)
				return false;
			
		}
		return true;

	}
	public static void addProperty(LinkedHashMap<String, ?> linkedHashMap){
		Property current = new Property(); 		
		current.setName((ArrayList<String>)linkedHashMap.get("name"));
		current.setDescription((String)linkedHashMap.get("description"));
		current.setScope((ArrayList<String>)linkedHashMap.get("scope"));		  
		  
		allprops.add(current);
		
	}
}
