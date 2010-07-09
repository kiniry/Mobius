/**
 * @title "Semantic Property Plugin Package"
 * @description "Class that holds all properties in one structure."
 * @author  Eoin O'Connor
 * @copyright ""
 * @license "Public Domain."
 * @version "$Id: 01-07-2010 $"
 */
package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;

import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;

import custom_yaml.CustomConstructor;
import custom_yaml.CustomRepresenter;
import custom_yaml.CustomResolver;

/**
 * <p>
 * A class that takes yaml files,parses them with snakeyaml and constructs and
 * stores the appropiate semantic properties
 * </p>
 * 
 * @see Property
 * @see RegExpStruct
 * @version "$Id: 01-07-2010 $"
 * @author Eoin O'Connor
 **/
public class FileChecker {

	// Attributes

	private static List<Property> allprops;
	private File input;

	/**
	 * 
	 * @param yaml
	 *            file
	 */
	public FileChecker(File inputFile) {
		allprops = new LinkedList<Property>();
		input = inputFile;
		parseFile(input);
	}

	/**
	 * <p>
	 * method that prints the name,regexp and map of each regular expression.
	 * Used for testing
	 * </p>
	 */
	public void printProps() {
		for (Property p : allprops) {
			System.out.println(p);
			System.out
					.println("Regular expression is " + (p.getReg()).getExp());
			System.out.println("Regular expression map is "
					+ (p.getReg()).getGroups());
		}
	}

	public List<Property> getProps() {
		return allprops;
	}

	/**
	 * 
	 * @return list of the regexp of all the properties
	 */
	public LinkedList<RegExpStruct> getAllRegExp() {
		LinkedList<RegExpStruct> r = new LinkedList<RegExpStruct>();
		for (Property p : allprops) {
			r.add(p.getReg());
		}
		return r;

	}

	/**
	 * <p>
	 * parser a file using snakeyaml and creates the appropiate properties
	 * </p>
	 * 
	 * @param inputFile
	 *            yaml file to parse, may contain multiple properties
	 */
	private static void parseFile(File inputFile) {

		// get input stream from file;
		InputStream input = null;
		try {
			input = new FileInputStream(inputFile);
		} catch (FileNotFoundException e) {
			System.out.println("error reading from " + inputFile + " file");
			e.printStackTrace();
			System.exit(1);
		}
		// create snakeyaml pbject
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
				new CustomRepresenter(), new DumperOptions()),
				new CustomResolver());
		// create yaml object with snakeyaml
		Object data = yaml.loadAll(input);

		try {
			Iterable s = (Iterable<Object>) data;
			Iterator<LinkedHashMap<String, ?>> i;
			i = s.iterator();
			// iterate through the properties and add them
			while (i.hasNext()) {
				//allprops.add(new Property(i.next()));
			}
		} catch (Exception e) {
			System.out.println("yaml file " + input
					+ " did not contain expected Iterators, invalid yaml file");
			e.printStackTrace();
		}

	}

	/**
	 * 
	 * @return true when the input is a valid instance of one of the semantic
	 *         properties in this filechecker
	 */

	public boolean check(String input) {
		// get name of property from input
		int i = input.indexOf(" ");
		String search = input.substring(0, i);

		// loop through properties
		for (Property current : allprops) {
			// check if cuurent property has same name as input and parse if it
			// does
			if (current.getName().equals(search)) {
				return current.isProperty(input);
			}
		}
		// case where no properties name match the input property name
		return false;

	}

}
