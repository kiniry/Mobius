package ie.ucd.semanticproperties.plugin.yaml;

import ie.ucd.semanticproperties.plugin.customobjects.*;

import org.yaml.snakeyaml.nodes.Node;
import org.yaml.snakeyaml.nodes.Tag;
import org.yaml.snakeyaml.representer.Represent;
import org.yaml.snakeyaml.representer.Representer;


public class CustomRepresenter extends Representer {
    public CustomRepresenter() {
        this.representers.put(Nat.class, new RepresentNat());
        this.representers.put(MyInt.class, new RepresentMyInt());
        this.representers.put(MyFloat.class, new RepresentMyFloat());
        this.representers.put(MyClass.class, new RepresentMyClass());
        this.representers.put(MyDate.class, new RepresentMyDate());
        this.representers.put(MyDescription.class, new RepresentMyDescription());
        this.representers.put(MyEmail.class, new RepresentMyEmail());
        this.representers.put(MyExpression.class, new RepresentMyExpression());
        this.representers.put(MyString.class, new RepresentMyString());
        this.representers.put(MyThrowable.class, new RepresentMyThrowable());
        this.representers.put(MyURL.class, new RepresentMyURL());
        this.representers.put(MyVersion.class, new RepresentMyVersion());
        
    }

    private class RepresentNat implements Represent {
        public Node representData(Object data) {
            Nat nat = (Nat) data;
            String value = "<"+nat.getId()+"=nat>";
            return representScalar(new Tag("!nat"), value);
        }
    }
    private class RepresentMyInt implements Represent {
        public Node representData(Object data) {
            MyInt myint = (MyInt) data;
            String value = "<"+myint.getId()+"=myint>";
            return representScalar(new Tag("!myint"), value);
        }
    }
    private class RepresentMyFloat implements Represent {
        public Node representData(Object data) {
            MyFloat myfloat = (MyFloat) data;
            String value = "<"+myfloat.getId()+"=myfloat>";
            return representScalar(new Tag("!myfloat"), value);
        }
    }
    private class RepresentMyClass implements Represent {
        public Node representData(Object data) {
            MyClass myclass = (MyClass) data;
            String value = "<"+myclass.getId()+"=myclass>";
            return representScalar(new Tag("!myclass"), value);
        }
    }
    private class RepresentMyDate implements Represent {
        public Node representData(Object data) {
            MyDate eg = (MyDate) data;
            String value = "<"+eg.getId()+"=mydate>";
            return representScalar(new Tag("!mydate"), value);
        }
    }
    private class RepresentMyDescription implements Represent {
        public Node representData(Object data) {
            MyDescription eg = (MyDescription) data;
            String value = "<"+eg.getId()+"=mydescription>";
            return representScalar(new Tag("!mydescription"), value);
        }
    }
    private class RepresentMyEmail implements Represent {
        public Node representData(Object data) {
            MyEmail eg = (MyEmail) data;
            String value = "<"+eg.getId()+"=myemail>";
            return representScalar(new Tag("!myemail"), value);
        }
    }
    private class RepresentMyExpression implements Represent {
        public Node representData(Object data) {
            MyExpression eg = (MyExpression) data;
            String value = "<"+eg.getId()+"=myexpression>";
            return representScalar(new Tag("!myexpression"), value);
        }
    }
    private class RepresentMyString implements Represent {
        public Node representData(Object data) {
            MyString eg = (MyString) data;
            String value = "<"+eg.getId()+"=mystring>";
            return representScalar(new Tag("!mystring"), value);
        }
    }
    private class RepresentMyThrowable implements Represent {
        public Node representData(Object data) {
            MyThrowable eg = (MyThrowable) data;
            String value = "<"+eg.getId()+"=mythrowable>";
            return representScalar(new Tag("!mythrowable"), value);
        }
    }
    private class RepresentMyVersion implements Represent {
        public Node representData(Object data) {
            MyVersion eg = (MyVersion) data;
            String value = "<"+eg.getId()+"=myversion>";
            return representScalar(new Tag("!myversion"), value);
        }
    }    private class RepresentMyURL implements Represent {
        public Node representData(Object data) {
            MyURL eg = (MyURL) data;
            String value = "<"+eg.getId()+"=myurl>";
            return representScalar(new Tag("!myurl"), value);
        }
    }
}