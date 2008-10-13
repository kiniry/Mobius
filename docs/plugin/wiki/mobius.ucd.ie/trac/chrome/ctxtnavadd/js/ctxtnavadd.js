function find_old_last() {
    var ctxtnav = document.getElementById('ctxtnav');
    for (var i in ctxtnav.childNodes) {
        if(ctxtnav.childNodes[i].tagName == 'UL') {
            var ul_node = ctxtnav.childNodes[i];
            for (var j in ul_node.childNodes) {
                if(ul_node.childNodes[j].tagName == 'LI') {
                    var li_node = ul_node.childNodes[j];
                    if(li_node.getAttribute('class') == 'last') {
                        return(li_node);
                    }
                }
            }
        }
    }
}

function add_ctxtnav(txt) {
    // Make a new <li> and find the old <li class="last">
    var new_li = document.createElement('LI');
    var old_li = find_old_last();

    // Insert content
    new_li.innerHTML = txt;
    
    // Set the class on the new <li> and clear the old one
    new_li.setAttribute('class','last');
    old_li.removeAttribute('class');

    // Insert the new node
    old_li.parentNode.appendChild(new_li);
}


function add_ctxtnav_link(href, txt) {
    var html = '<a href="' + href + '">' + txt + '</a>';
    add_ctxtnav(html);
}
