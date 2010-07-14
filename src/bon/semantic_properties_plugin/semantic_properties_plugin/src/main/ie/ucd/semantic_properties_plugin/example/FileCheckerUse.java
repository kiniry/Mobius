package ie.ucd.semantic_properties_plugin.example;

import ie.ucd.semantic_properties_plugin.file_checker.FileChecker;

import java.io.File;
import java.io.FileInputStream;
import java.net.URI;
import java.util.LinkedHashMap;

import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;

import custom_yaml.CustomConstructor;
import custom_yaml.CustomRepresenter;
import custom_yaml.CustomResolver;

public class FileCheckerUse {
	public static void main(String[] args) {
		File caseOne= new File("resources/examples/eg1.yaml");
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
				new CustomRepresenter(), new DumperOptions()),
				new CustomResolver());;
		FileInputStream io=null;

		try {
			io = new FileInputStream(caseOne);
		} catch (Exception e) {
			System.out.println("invalid string");
		}

		Object ob = yaml.load(io);
		String l = yaml.dump(ob);
		System.out.println(l);
		

	}


	
}
