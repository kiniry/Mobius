package escjava.gui;

public class TaskQueue {

    private java.util.LinkedList tasks = new java.util.LinkedList();

    synchronized public void addTask(Object o) { 
	tasks.addLast(o); 
	notifyAll();
    }

    synchronized public Object getTask() { 
	while (tasks.isEmpty()) {
	    try { wait(); } catch (Exception e) {}
	}
	return tasks.removeFirst(); 
    }

    synchronized public void clear() {
	tasks.clear();
    }
}
