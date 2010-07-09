package ie.ucd.semantic_properties_plugin.example;

import ie.ucd.semantic_properties_plugin.file_checker.FileChecker;

import java.io.File;
import java.net.URI;

public class FileCheckerUse {
	public static void main(String[] args){
		File caseOne= new File("resources/examples/correctexample2.yaml");
		FileChecker checkOne= new FileChecker(caseOne);


//		File caseTwo= new File("resources/examples/yamlexample1.yaml");
//		FileChecker checkTwo= new FileChecker(caseTwo);
//		checkTwo.processFile();
//		checkTwo.printProps();
//	
	}


	
}
