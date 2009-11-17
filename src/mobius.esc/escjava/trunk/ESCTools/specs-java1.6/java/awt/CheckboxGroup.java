package java.awt;

public class CheckboxGroup implements java.io.Serializable {
    Checkbox selectedCheckbox = null;
    private static final long serialVersionUID = 3729780091441768983L;
    
    public CheckboxGroup() {
        
    }
    
    public Checkbox getSelectedCheckbox() {
        return getCurrent();
    }
    
    
    public Checkbox getCurrent() {
        return selectedCheckbox;
    }
    
    public void setSelectedCheckbox(Checkbox box) {
        setCurrent(box);
    }
    
    
    public synchronized void setCurrent(Checkbox box) {
        if (box != null && box.group != this) {
            return;
        }
        Checkbox oldChoice = this.selectedCheckbox;
        this.selectedCheckbox = box;
        if (oldChoice != null && oldChoice != box && oldChoice.group == this) {
            oldChoice.setState(false);
        }
        if (box != null && oldChoice != box && !box.getState()) {
            box.setStateInternal(true);
        }
    }
    
    public String toString() {
        return getClass().getName() + "[selectedCheckbox=" + selectedCheckbox + "]";
    }
}
