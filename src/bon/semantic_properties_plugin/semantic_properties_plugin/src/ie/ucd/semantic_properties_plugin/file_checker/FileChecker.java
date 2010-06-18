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

	
	static List<Property> allprops;

	// for testing purposes
	final static String regEx = ".*+";

	public static void main(String[] args) throws FileNotFoundException {
		//initialise values
		allprops= new LinkedList<Property>();
		
		//parse in yaml file
		parseFile(getInputFile());
		
		// check the validity
		if(checkvalidity()){
			System.out.println("This Semantic Property is valid");
			}
		else{
			System.out.println("This Semantic Property is invalid");
		}
		

	}

	private static String getInputFile() {
		
		
		// get name of file
		System.out.println("enter file name (from resources/examples/ folder)");	
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

	private static void parseFile(String inputfile) {
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
//		
//		if(data instanceof LinkedHashMap<?, ?>){
//			System.out.println("is linkedhashmap");
//			LinkedHashMap<String,?> h;
//			h = (LinkedHashMap<String,?>)data;
//			System.out.println(h.toString());
//		}
		if(data instanceof Iterable){
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
			System.out.println("yaml file "+input+" did not contain expected Iterator");
		}

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
