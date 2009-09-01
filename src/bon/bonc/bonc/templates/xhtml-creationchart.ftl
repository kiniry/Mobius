<div class="top-level" id="creation_chart:${id}">
  <table class="outer">
    <tr class="top">
      <th class="type">CREATION</th>
      <td class="name" colspan="2">${name}</td>
      <td class="part"><strong>Part:</strong> ${part!"1/1"}</td>
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
            <th class="grey">Creates instances of</th>
          </tr>
<#list entries as entry>          <tr>
            <td class="light-grey">${entry.name.name}</td>
            <td class="white"><#list entry.types as type>${type}<#if type_has_next>, </#if></#list></td>
          </tr></#list>
        </table>
      </td>
    </tr>
  </table>
</div>
