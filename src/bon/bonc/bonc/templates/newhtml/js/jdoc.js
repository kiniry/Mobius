

function setup() {
  $j('#search-box').val('Search...');
  
  var initialHash = $j.history.getCurrent();
  processHash(initialHash);
  $j(document).history(function(e,curr,prev) { processHash(curr); });

  var autocompleter = new Autocompleter.Local('search-box', 'search-results', elements_list, {updateElement: selectedAuto, partialChars: 1, fullSearch: true});
  
  $j('#search-box').focus(function(event){
    $('search-box').morph('width: 500px; font-size: 20px;', {duration: 0.2});
    $('search-pane').morph('width: 500px; font-size: 20px;', {duration: 0.2});
    $('main-display').morph('opacity: 0.1', {duration: 0.2});
    if ($j('#search-box').val() == 'Search...') {
      $j('#search-box').val('');
    } else if ($j('#search-box').val() != '') {
      setTimeout(function(){ autocompleter.show(); }, 250);
    }
  });
  
  //On search box lose focus, restore search box (and  small size
  $j('#search-box').blur(function(event){
    $('search-box').morph('width: 150px; font-size: 12px;', {duration: 0.2});
    $('search-pane').morph('width: 200px; font-size: 20px;', {duration: 0.2});
    $('main-display').morph('opacity: 1', {duration: 0.2});
    if ($j('#search-box').val() == '') {
      $j('#search-box').val('Search...');
    }
  });
  
  $j(document).bind('keydown', {combi: '/', disableInInput: true}, function() {
    $j('#search-box').focus();
    return false;
  });
  
  $j(document).bind('keydown', 'esc', function() {
    $j('#search-box').blur();
  });

};

function selectedAuto(selectedElement) {
  var value = Element.collectTextNodesIgnoreClass(selectedElement, 'informal');
  userLoadClass(value);
  $j('#search-box').blur(); 
}

function processHash(hash) {
  var parts = hash.split(':');
  if (parts.length >= 2) {
    loadClass(parts[1]);
  }
}

function userLoadClass(qualifiedClassname) {
 $j.history.add('class:' + qualifiedClassname);
 loadClass(qualifiedClassname);
}

function loadClass(qualifiedClassname) {
  $j('#main-display').load(qualifiedClassname + '.html');
  $j('#related').load(qualifiedClassname + '-related.html');
}

function navTo(loc) {
  var parts = loc.split(':');
  if (parts.length >= 2) {
    if (parts[0] == 'class') {
      userLoadClass(parts[1]);
    }
  }
  return false;
}