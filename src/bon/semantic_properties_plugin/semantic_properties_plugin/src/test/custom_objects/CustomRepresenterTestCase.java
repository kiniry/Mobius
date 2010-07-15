package custom_objects;


import junit.framework.TestCase;


import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;

import custom_yaml.CustomConstructor;
import custom_yaml.CustomRepresenter;
import custom_yaml.CustomResolver;

import semantic_properties_plugin.custom_objects.MyFloat;
import semantic_properties_plugin.custom_objects.MyInt;
import semantic_properties_plugin.custom_objects.Nat;

public class CustomRepresenterTestCase extends TestCase{


	
	public void testNatToDump() {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(new CustomRepresenter(), new DumperOptions()),	new CustomResolver());
		
		Nat sampleNat = new Nat();
		sampleNat.setId("andy");
		
			
		String output = yaml.dump(sampleNat);
		// this test is affected by the resolver
		String properOutput="<andy=nat>\n";
		assertEquals(properOutput, output);
	}
	public void testMyIntToDump() {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(new CustomRepresenter(), new DumperOptions()),	new CustomResolver());
		
		MyInt sampleMyInt = new MyInt();
		sampleMyInt.setId("andy");
		
			
		String output = yaml.dump(sampleMyInt);
		// this test is affected by the resolver
		String properOutput="<andy=myint>\n";
		assertEquals(properOutput, output);
	}

	public void testMyFloatToDump() {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(new CustomRepresenter(), new DumperOptions()),	new CustomResolver());
		
		MyFloat sampleMyFloat = new MyFloat();
		sampleMyFloat.setId("andy");
		
			
		String output = yaml.dump(sampleMyFloat);
		// this test is affected by the resolver
		String properOutput="<andy=myfloat>\n";
		assertEquals(properOutput, output);
	}
	
	
}
