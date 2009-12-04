var class_list = [
<#list fclasses as fclass>
{ name: '${fclass.name.name}', cluster: '${STUtil.getQualifiedClusterStringForClass(fclass,st)}',
<#assign features=STUtil.getFeaturesForClass(fclass,st)/>
  features: [ <#list features as feature>'${feature.a}'<#if feature_has_next>, </#if></#list> ] }<#if fclass_has_next>, </#if></#list>
];
var cluster_list = [<#list fclusters as fcluster>'${fcluster.name}'<#if fcluster_has_next>, </#if></#list>];
var elements_list = class_list; //jQuery.merge(class_list, cluster_list);