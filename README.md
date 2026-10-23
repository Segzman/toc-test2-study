# Theory of Computation — Test 2 study site

Refresher → easy flood → Easy-to-Crazy ramp → mock test (12 MCQ + 4 written + bonus).
Plus a visual pumping-lemma explainer. Regex, regex ↔ state diagrams, “show R is regular” proofs, pumping lemma, CFGs, DFA → CFG.

## Run it on a Mac

Open **Terminal** (⌘ Space → type “Terminal” → Enter), paste this, press Enter:

```bash
mkdir -p ~/toc-test2-study && cd ~/toc-test2-study && for f in index.html pumping.html core.js; do curl -fsSL "https://raw.githubusercontent.com/Segzman/toc-test2-study/main/$f" -o "$f"; done && open index.html pumping.html
```

It opens both sites in your browser:
- **index.html** — practice site (refresher, easy flood, Easy → Crazy, mock test)
- **pumping.html** — visual pumping-lemma explainer (short method, break-it game, why regular languages survive)

Next time: `open ~/toc-test2-study/index.html ~/toc-test2-study/pumping.html` (or paste the line again to get updates).

Keys: **L** refresher · **Q** questions · **W** written · **1–4** answer · **Enter** next · **Space** next step.
Progress is saved in your browser.
