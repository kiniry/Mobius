package ie.ucd.semantic_properties_plugin.file_checker;

import java.util.LinkedHashMap;
import java.util.Map;

import junit.framework.TestCase;

import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;


public class CustomResolverTestCase extends TestCase{
	
	protected void setUp() {

    }

	
	public void testNatResolver() {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
				new CustomRepresenter(), new DumperOptions()),
				new CustomResolver());
		
		Nat  standardNat= new Nat();
		standardNat.setId("example");
		
		
		Object implicitData = yaml.load("{sem: <example=nat>}");
		Object explicitData= yaml.load("{sem: !nat <example=nat>}");
		
		LinkedHashMap implic=(LinkedHashMap<String,Nat>)implicitData;
		LinkedHashMap explic=(LinkedHashMap<String,Nat>)explicitData;
		
		assertEquals((Nat)explic.get("sem"),standardNat);
		assertEquals((Nat)implic.get("sem"),(Nat)explic.get("sem"));

	}
	
	public void testMyIntResolver() {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
				new CustomRepresenter(), new DumperOptions()),
				new CustomResolver());
		
		MyInt  standardMyInt= new MyInt();
		standardMyInt.setId("example");
		
		
		Object implicitData = yaml.load("{sem: <example=myint>}");
		Object explicitData= yaml.load("{sem: !myint <example=myint>}");
		
		LinkedHashMap implic=(LinkedHashMap<String,MyInt>)implicitData;
		LinkedHashMap explic=(LinkedHashMap<String,MyInt>)explicitData;
		
		assertEquals((MyInt)explic.get("sem"),standardMyInt);
		assertEquals((MyInt)implic.get("sem"),(MyInt)explic.get("sem"));

	}


}
