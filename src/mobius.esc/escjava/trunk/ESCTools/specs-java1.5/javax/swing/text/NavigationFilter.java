package javax.swing.text;

public class NavigationFilter {
    
    public NavigationFilter() {
        
    }
    
    public void setDot(NavigationFilter$FilterBypass fb, int dot, Position$Bias bias) {
        fb.setDot(dot, bias);
    }
    
    public void moveDot(NavigationFilter$FilterBypass fb, int dot, Position$Bias bias) {
        fb.moveDot(dot, bias);
    }
    
    public int getNextVisualPositionFrom(JTextComponent text, int pos, Position$Bias bias, int direction, Position$Bias[] biasRet) throws BadLocationException {
        return text.getUI().getNextVisualPositionFrom(text, pos, bias, direction, biasRet);
    }
    {
    }
}
