package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.yaml.snakeyaml.Yaml;

public class FileChecker {

	/**
	 * @param args
	 */

	final static String prop_Scope = "property_scope(\\s)*:(\\s)*( files | modules | features | variables | all | special )(,( files | modules | features | variables | all | special ))*";

	final static String regEx = ".*";
	final static String prop_Form = "(\\w*) ( (\\w)* | (<(\\w)*>)* | ( \\( \\w \\) )* )* ((e? | (| e)?))";

	public static void main(String[] args) throws FileNotFoundException {
		
		String input = getInputFile();
		String dump = parseFile(input);
		input = getInputFile();
		dump = parseFile(input);

		// checkvalidity(dump);

	}

	private static String getInputFile() {
		System.out.println("what file");
		BufferedReader br = new BufferedReader(new InputStreamReader(System.in));

		String inputfile = null;

		try {
			inputfile = br.readLine();
		} catch (IOException ioe) {
			System.out.println("IO error trying to read your name!");
			System.exit(1);
		}
		return inputfile;
	}

	private static String parseFile(String inputfile) {
		InputStream input = null;
		try {
			input = new FileInputStream(new File(inputfile));
		} catch (FileNotFoundException e) {
			System.out.println("IO error reading from " + inputfile + " file");
			e.printStackTrace();
			System.exit(1);
		}
		Yaml yaml = new Yaml();
		Object data = yaml.load(input);

		String stringdump = yaml.dump(data);

		System.out.print(stringdump);
		return stringdump;

	}

	private static boolean checkvalidity(String input) {

		Pattern pattern = Pattern.compile(regEx);

		Matcher matcher = pattern.matcher(input);

		boolean found = false;
		while (matcher.find()) {

			found = true;
		}
		if (!found) {
			System.out.println("No match found.%n");
		} else {
			System.out.println("Valid RegExp");
		}
		return found;

	}
}
