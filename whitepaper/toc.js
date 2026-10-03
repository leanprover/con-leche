// whitepaper/toc.js — inlined by lib.typ's template into the HTML.
// Progressive enhancement for the table of contents (aside.toc, a
// <details> around Typst's <nav role="doc-toc">): without it the ToC
// is a plain list of links, open.  With it
//   * the <details> follows the viewport: open in the wide layout
//     (where style.css makes it a sticky sidebar), closed in the narrow
//     one, and closed again after a link is followed there;
//   * the entry of the section in view carries `.current` (its parent
//     section `.current-parent`), kept scrolled into the sidebar's view.
// "In view": the last heading at or above 30% of the viewport height
// (the first heading while the title block is still being read), or
// the last heading of all once the end of the article is visible.
// An IntersectionObserver on the headings (its root margin is that 30%
// band) and one on the article's last element fire the recomputation.
(function () {
  var toc = document.querySelector('aside.toc');
  var main = document.querySelector('main');
  if (!toc || !main) return;
  var details = toc.querySelector('details');
  var wide = window.matchMedia('(min-width: 1100px)');

  function fit() { if (details) details.open = wide.matches; }
  fit();
  if (wide.addEventListener) wide.addEventListener('change', fit);
  toc.addEventListener('click', function (ev) {
    var a = ev.target.closest ? ev.target.closest('a[href]') : null;
    if (a && details && !wide.matches) details.open = false;
  });

  var byId = {};
  var links = toc.querySelectorAll('a[href^="#"]');
  for (var i = 0; i < links.length; i++) {
    byId[links[i].getAttribute('href').slice(1)] = links[i];
  }
  var heads = [];
  var hs = main.querySelectorAll('h2[id], h3[id]');
  for (var j = 0; j < hs.length; j++) {
    if (byId[hs[j].id]) heads.push(hs[j]);
  }
  if (heads.length === 0) return;
  var last = main.lastElementChild;

  var current = null, parent = null;
  function parentLink(a) {
    var li = a.closest('ol').closest('li');
    return li ? li.querySelector('a') : null;
  }
  function reveal(a) {
    if (!wide.matches) return;
    var r = a.getBoundingClientRect(), n = toc.getBoundingClientRect();
    var pad = 24;
    if (r.top < n.top + pad) toc.scrollTop += r.top - n.top - pad;
    else if (r.bottom > n.bottom - pad) toc.scrollTop += r.bottom - n.bottom + pad;
  }
  function update() {
    var limit = window.innerHeight * 0.3;
    var h = heads[0];
    for (var k = 0; k < heads.length; k++) {
      if (heads[k].getBoundingClientRect().top <= limit) h = heads[k];
      else break;
    }
    if (last && last.getBoundingClientRect().bottom <= window.innerHeight + 1) {
      h = heads[heads.length - 1];
    }
    var a = h ? byId[h.id] : null;
    if (a === current) return;
    if (current) current.classList.remove('current');
    if (parent) parent.classList.remove('current-parent');
    current = a;
    parent = a ? parentLink(a) : null;
    if (parent && parent !== a) parent.classList.add('current-parent'); else parent = null;
    if (current) { current.classList.add('current'); reveal(current); }
  }

  if ('IntersectionObserver' in window) {
    var io = new IntersectionObserver(update, { rootMargin: '0px 0px -70% 0px' });
    for (var m = 0; m < heads.length; m++) io.observe(heads[m]);
    if (last) new IntersectionObserver(update).observe(last);
  } else {
    window.addEventListener('scroll', update, { passive: true });
  }
  window.addEventListener('resize', update);
  window.addEventListener('load', update);
  update();
})();
