package custom_yaml;

import java.util.regex.Pattern;

import org.yaml.snakeyaml.nodes.Tag;
import org.yaml.snakeyaml.resolver.Resolver;

import semantic_properties_plugin.custom_objects.MyObjectKind;

public class CustomResolver extends Resolver {

	protected void addImplicitResolvers() {
		addImplicitResolver(new Tag("!nat"), Pattern.compile("<\\w+=nat="+MyObjectKind.Nat.getReg()+">"), null);
		addImplicitResolver(new Tag("!myint"), Pattern.compile("<\\w+=int="+MyObjectKind.MyInt.getReg()+">"), null);
		addImplicitResolver(new Tag("!myfloat"), Pattern.compile("<\\w+=float="+MyObjectKind.MyFloat.getReg()+">"), null);
		addImplicitResolver(new Tag("!myclass"), Pattern.compile("<\\w+=class="+MyObjectKind.Class.getReg()+">"), null);
		addImplicitResolver(new Tag("!mydate"), Pattern.compile("<\\w+=date="+MyObjectKind.Date.getReg()+">"), null);
		addImplicitResolver(new Tag("!mydescription"), Pattern.compile("<\\w+=description="+MyObjectKind.Description.getReg()+">"), null);
		addImplicitResolver(new Tag("!myemail"), Pattern.compile("<\\w+=email="+MyObjectKind.Email.getReg()+">"), null);
		addImplicitResolver(new Tag("!myexpression"), Pattern.compile("<\\w+=expression="+MyObjectKind.Expression.getReg()+">"), null);
		addImplicitResolver(new Tag("!mystring"), Pattern.compile("<\\w+=string="+MyObjectKind.String.getReg()+">"), null);
		addImplicitResolver(new Tag("!mythrowable"), Pattern.compile("<\\w+=throwable="+MyObjectKind.Throwable.getReg()+">"), null);
		addImplicitResolver(new Tag("!myurl"), Pattern.compile("<\\w+=url="+MyObjectKind.URL.getReg()+">"), null);
		addImplicitResolver(new Tag("!myversion"), Pattern.compile("<\\w+=version="+MyObjectKind.Version.getReg()+">"), null);		
		
//		addImplicitResolver(Tag.BOOL, BOOL, "yYnNtTfFoO");
//		addImplicitResolver(Tag.FLOAT, FLOAT, "-+0123456789.");
//		addImplicitResolver(Tag.INT, INT, "-+0123456789");
//		addImplicitResolver(Tag.MERGE, MERGE, "<");
//		addImplicitResolver(Tag.NULL, NULL, "~nN\0");
//		addImplicitResolver(Tag.NULL, EMPTY, null);
//		addImplicitResolver(Tag.TIMESTAMP, TIMESTAMP, "0123456789");
//		addImplicitResolver(Tag.VALUE, VALUE, "=");
	}
}