(() => {
  const tabs = [...document.querySelectorAll('.tab')];
  if (!tabs.length) return;
  const cards = [...document.querySelectorAll('.card')];
  const empties = [...document.querySelectorAll('.empty')];
  const proved = document.getElementById('only-proved');
  const tr = document.getElementById('only-tr');
  let subject = 'all';
  try { subject = localStorage.getItem('subject') || 'all'; } catch (e) {}
  function apply() {
    tabs.forEach(t => t.classList.toggle('on', t.dataset.subject === subject));
    cards.forEach(c => {
      c.hidden = !((subject === 'all' || c.dataset.subject === subject) &&
        (!proved.checked || c.dataset.lean === 'proved') &&
        (!tr.checked || c.dataset.tr !== 'none'));
    });
    empties.forEach(e => { e.hidden = e.dataset.subject !== subject; });
    try { localStorage.setItem('subject', subject); } catch (e) {}
  }
  tabs.forEach(t => t.addEventListener('click', () => { subject = t.dataset.subject; apply(); }));
  [proved, tr].forEach(x => x.addEventListener('change', apply));
  apply();
})();
