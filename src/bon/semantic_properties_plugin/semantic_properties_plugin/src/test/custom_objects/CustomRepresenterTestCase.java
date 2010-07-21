package custom_objects;


import ie.ucd.semanticproperties.plugin.customobjects.MyFloat;
import ie.ucd.semanticproperties.plugin.customobjects.MyInt;
import ie.ucd.semanticproperties.plugin.customobjects.Nat;
import ie.ucd.semanticproperties.plugin.yaml.CustomConstructor;
import ie.ucd.semanticproperties.plugin.yaml.CustomRepresenter;
import ie.ucd.semanticproperties.plugin.yaml.CustomResolver;
import junit.framework.TestCase;


import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;



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
