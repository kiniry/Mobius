package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.*;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.Iterator;

import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;
import org.yaml.snakeyaml.constructor.Constructor;
import org.yaml.snakeyaml.resolver.Resolver;
import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;


public class FileChecker {

	
	static List<Property> allprops;

	// for testing purposes
	final static String regEx = ".*+";

	public static void main(String[] args) throws FileNotFoundException {
		//initialise values
		allprops= new LinkedList<Property>();
		

		
//		
//		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(new DumperOptions()), new CustomResolver());
//		Object data= (Object)yaml.load(getInputFile());
		
		
		//parse in yaml file
		//parseFile(getInputFile());
		
		// check the validity
//		if(checkvalidity()){
//			System.out.println("This Semantic Property is valid");
//			}
//		else{
//			System.out.println("This Semantic Property is invalid");
//		}
//		
		
		

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
		//get input stream from file
		InputStream input = null;
		try {
			input = new FileInputStream(new File("resources/examples/"+inputfile));
		} catch (FileNotFoundException e) {
			System.out.println("error reading from " + inputfile + " file");
			e.printStackTrace();
			System.exit(1);
		}
	
//		delete in a bit
//		Loader l= new Loader(new Constructor(testprop.class));
//		Yaml yaml = new Yaml(l);
//		testprop data = (testprop)yaml.loadAll(input);
		
		
		Yaml yaml = new Yaml();
		
		Object data = yaml.loadAll(input);
		
		if(data instanceof Iterable){
			Iterator<LinkedHashMap<String,?>> i;
			//iterate through the properties and add them
			
			Iterable s=(Iterable<Object>)data;
			i=s.iterator();
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
		current.setName((ArrayList<Object>)linkedHashMap.get("name"));
		current.setDescription((String)linkedHashMap.get("description"));
		current.setScope((ArrayList<String>)linkedHashMap.get("scope"));		  
		  
		allprops.add(current);
		
	}
}
