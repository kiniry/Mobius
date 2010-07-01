package ie.ucd.semantic_properties_plugin.file_checker;

import java.util.regex.Pattern;

import org.yaml.snakeyaml.nodes.Tag;
import org.yaml.snakeyaml.resolver.Resolver;

public class CustomResolver extends Resolver {

	protected void addImplicitResolvers() {
		addImplicitResolver(new Tag("!nat"), Pattern.compile("<\\w+=nat>"), null);
		addImplicitResolver(new Tag("!myint"), Pattern.compile("<\\w+=myint>"), null);
		addImplicitResolver(new Tag("!myfloat"), Pattern.compile("<\\w+=myfloat>"), null);
		addImplicitResolver(new Tag("!myclass"), Pattern.compile("<\\w+=myclass>"), null);
		addImplicitResolver(new Tag("!mydate"), Pattern.compile("<\\w+=mydate>"), null);
		addImplicitResolver(new Tag("!mydescription"), Pattern.compile("<\\w+=mydescription>"), null);
		addImplicitResolver(new Tag("!myemail"), Pattern.compile("<\\w+=myemail>"), null);
		addImplicitResolver(new Tag("!myexpression"), Pattern.compile("<\\w+=myexpression>"), null);
		addImplicitResolver(new Tag("!mystring"), Pattern.compile("<\\w+=mystring>"), null);
		addImplicitResolver(new Tag("!mythrowable"), Pattern.compile("<\\w+=mythrowable>"), null);
		addImplicitResolver(new Tag("!myurl"), Pattern.compile("<\\w+=myurl>"), null);
		addImplicitResolver(new Tag("!myversion"), Pattern.compile("<\\w+=myversion>"), null);		
		
		addImplicitResolver(Tag.BOOL, BOOL, "yYnNtTfFoO");
		addImplicitResolver(Tag.FLOAT, FLOAT, "-+0123456789.");
		addImplicitResolver(Tag.INT, INT, "-+0123456789");
		addImplicitResolver(Tag.MERGE, MERGE, "<");
		addImplicitResolver(Tag.NULL, NULL, "~nN\0");
		addImplicitResolver(Tag.NULL, EMPTY, null);
		addImplicitResolver(Tag.TIMESTAMP, TIMESTAMP, "0123456789");
		addImplicitResolver(Tag.VALUE, VALUE, "=");
	}
}