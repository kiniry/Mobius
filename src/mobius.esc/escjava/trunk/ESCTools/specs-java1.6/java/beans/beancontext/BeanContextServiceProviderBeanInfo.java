package java.beans.beancontext;

import java.beans.BeanInfo;

public interface BeanContextServiceProviderBeanInfo extends BeanInfo {
    
    BeanInfo[] getServicesBeanInfo();
}
