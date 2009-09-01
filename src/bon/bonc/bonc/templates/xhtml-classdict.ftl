<div class="top-level" id="class_dictionary:${id}">
  <table class="outer">
    <tr class="top">
      <th class="type">CLASS DICTIONARY</th>
      <td class="name" colspan="2">${systemName}</td>
      <td class="part"><strong>Part:</strong> 1/1</td>
    </tr>
    <tr class="middle">
      <td class="explanation" colspan="2">
        <dl>
          <dt>Comment</dt>
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
        <table>
          <tr>
            <th class="grey">Class</th>
            <th class="grey">Cluster</th>
            <th class="grey">Description</th>
          </tr>
<#list entries as entry>          <tr>
            <td class="light-grey">${entry.name}</td>
            <td class="light-grey"><#list entry.clusters as cluster>${cluster}<#if cluster_has_next> ,</#if></#list></td>
            <td class="white">${entry.name}</td>
          </tr></#list>
        </table>
      </td>
    </tr>
  </table>
</div>
