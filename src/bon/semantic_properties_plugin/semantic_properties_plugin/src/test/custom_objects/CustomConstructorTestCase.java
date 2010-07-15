package custom_objects;

import java.util.Map;

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


public class CustomConstructorTestCase extends TestCase{
	
	public void testNatConstructor() {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
				new CustomRepresenter(), new DumperOptions()),
				new CustomResolver());
		Nat sampleNat= new Nat("example",0);
		Object data = yaml.load("{samples: !nat '<example=nat>'}");
		Map<String, Nat> map = (Map<String, Nat>) data;
		
		assertEquals(sampleNat, map.get("samples"));

	}

	public void testMyIntConstructor() {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
				new CustomRepresenter(), new DumperOptions()),
				new CustomResolver());
		MyInt sampleMyInt= new MyInt("exampleMyInt",0);
		Object data = yaml.load("{samples: !myint '<exampleMyInt=MyInt>'}");
		Map<String, MyInt> map = (Map<String, MyInt>) data;
		
		assertEquals(sampleMyInt, map.get("samples"));

	}
	public void testMyFloatConstructor() {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
				new CustomRepresenter(), new DumperOptions()),
				new CustomResolver());
		MyFloat sampleMyFloat= new MyFloat("exampleMyFloat",0);
		Object data = yaml.load("{samples: !myfloat '<exampleMyFloat=myfloat>'}");
		Map<String, MyFloat> map = (Map<String, MyFloat>) data;
		
		assertEquals(sampleMyFloat, map.get("samples"));

	}

}
