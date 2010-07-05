package ie.ucd.semantic_properties_plugin.example;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class RegexChecker {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		
		Pattern p=Pattern.compile("(\\w+)\\s(\\w+)\\s(\\w+)");
		
		Matcher r= p.matcher("foo is cool");
		
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
