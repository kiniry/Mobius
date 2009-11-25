var class_list = [<#list fclasses as fclass>'${fclass.name.name}'<#if fclass_has_next>, </#if></#list>];
var cluster_list = [<#list fclusters as fcluster>'${fcluster.name}'<#if fcluster_has_next>, </#if></#list>];
var elements_list = jQuery.merge(class_list, cluster_list);