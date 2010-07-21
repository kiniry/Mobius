package ie.ucd.semanticproperties.plugin.example;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class RegexChecker {

	/**Class to check Regexs.
	 * @param args
	 */
	public static void main(String[] args) {

		Pattern p=Pattern.compile( 
				
				"concurrency[\\s+](SEQUENTIAL|GUARDED|CONCURRENT|TIMEOUT[\\s+](\\d+\\.?[0]*)[\\s+]([a-zA-Z$](?:[a-zA-Z_$0-9]+)(?:\\.[a-zA-Z_$](?:[a-zA-Z_$0-9]+))+)|FAILURE[\\s+]([a-zA-Z$](?:[a-zA-Z_$0-9]+)(?:\\.[a-zA-Z_$](?:[a-zA-Z_$0-9]+))+)|SPECIAL)(?:[\\s+]:'(.*)')?"
				);
		
		Matcher r= p.matcher("concurrency CONCURRENT 'This class is fully thread-safe.'");
		
		if(r.matches()){
			
			for(int i=1;i<r.groupCount()+1;i++){
				System.out.println(r.group(i));
				
			}
			System.out.println("hell yeah");
		}
		else
			System.out.println("uh oh");
		

	}

}
                                                                                                                                                                                                                          
	