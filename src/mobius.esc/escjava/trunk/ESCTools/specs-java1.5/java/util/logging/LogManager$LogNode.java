package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;

class LogManager$LogNode {
    HashMap children;
    Logger logger;
    LogManager$LogNode parent;
    
    LogManager$LogNode(LogManager$LogNode parent) {
        
        this.parent = parent;
    }
    
    void walkAndSetParent(Logger parent) {
        if (children == null) {
            return;
        }
        Iterator values = children.values().iterator();
        while (values.hasNext()) {
            LogManager$LogNode node = (LogManager$LogNode)(LogManager$LogNode)values.next();
            if (node.logger == null) {
                node.walkAndSetParent(parent);
            } else {
                LogManager.access$700(node.logger, parent);
            }
        }
    }
}
