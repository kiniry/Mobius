package java.security;

import java.io.*;
import java.util.*;
import java.lang.ref.*;
import java.lang.reflect.*;

class Provider$EngineDescription {
    final String name;
    final boolean constructor;
    final boolean supportsParameter;
    
    Provider$EngineDescription(String name, boolean constructor, boolean sp) {
        
        this.name = name;
        this.constructor = constructor;
        this.supportsParameter = sp;
    }
}
