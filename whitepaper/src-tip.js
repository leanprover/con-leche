// whitepaper/src-tip.js — inlined by lib.typ's template into the HTML.
// Progressive enhancement for the source tips (.src-wrap .src-tip): the
// CSS shows a tip on hover/focus anchored at the link; this shifts it
// left so it stays inside the viewport.  Written without the characters
// the Typst HTML export escapes (no angle brackets, no ampersand).
(function () {
  function place(ev) {
    var w = ev.target.closest ? ev.target.closest('.src-wrap') : null;
    if (!w) return;
    var t = w.querySelector('.src-tip');
    if (!t) return;
    t.style.left = '0px';
    var r = t.getBoundingClientRect();
    var margin = 8;
    var shift = -Math.max(0, r.right - window.innerWidth + margin);
    shift = Math.max(shift, margin - r.left);
    t.style.left = shift + 'px';
  }
  document.addEventListener('mouseover', place);
  document.addEventListener('focusin', place);
})();
