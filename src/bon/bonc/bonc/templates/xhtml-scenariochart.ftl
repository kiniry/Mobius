<div class="top-level" id="scenario_chart:${id}">
  <table class="outer">
    <tr class="top">
      <th class="type">SCENARIOS</th>
      <td class="name" colspan="2">${systemName}</td>
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
<#list entries as entry>          <tr>
            <td class="white">
              <dl class="scenario_entry">
                <dt>${entry.name}</dt>
                <dd>${entry.description}</dd>
              </dl>
            </td>
          </tr></#list>
        </table>
      </td>
    </tr>
  </table>
</div>
