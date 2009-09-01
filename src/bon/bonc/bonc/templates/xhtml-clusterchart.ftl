<div class="top-level" id="cluster_chart:${name}">
  <table class="outer">
    <tr class="top">
      <th class="type">CLUSTER</th>
      <td class="name" colspan="2">${name}</td>
      <td class="part"><strong>Part:</strong> ${part!"1/1"}</td>
    </tr>
    <tr class="middle">
      <td class="explanation" colspan="2">
        <dl>
          <dt>Purpose</dt>
          <dd>${explanation!""}</dd>
        </dl>
      </td>
      <td class="indexing" colspan="2">
        <dl>
          <dt>Indexing</dt>
<#if indexing??><#list indexing.indexes as indexitem>          <dd>${indexitem.id} : <#list indexitem.indexTerms as term>${term}<#if term_has_next>, </#if></#list>;</dd>
</#list></#if>
        </dl>
      </td>
    </tr>
    <tr>
      <td colspan="4" class="bottom">
        <#if (classes?size > 0)><table>
          <tr>
            <th class="grey">Class</th>
            <th class="grey">Description</th>
          </tr>
<#list classes as clazz>          <tr>
            <td class="light-grey">${clazz.name}</td>
            <td class="white">${clazz.description}</td>
          </tr></#list>
        </table>
        </#if><#if (clusters?size > 0)><table>
          <tr>
            <th>Cluster</th>
            <th>Description</th>
          </tr>
<#list clusters as cluster>          <tr>
            <td class="light-grey">${cluster.name}</td>
            <td class="white">${cluster.description}</td>
          </tr></#list>
        </table>
        </#if>
      </td>
    </tr>
  </table>
</div>
