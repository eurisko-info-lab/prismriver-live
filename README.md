# prismriver-live

**Live web editor for Lean 4 + Prismriver**  
Real-time LilyPond-style sheet music rendered directly from Prismriver DSL.

Study musical structures (Ravel’s *Boléro*, scales, counterpoint, etc.) with machine-checked Lean proofs **and** instant notation.

## Features
- Monaco-style Lean editor (dark theme)
- Live VexFlow score renderer (publication-quality, 3/4 time, repeats, dynamics)
- Pre-loaded *Boléro* examples (ostinato + themes + full form)
- One-click "Copy to real Lean" for live.lean-lang.org or Prismriver in VS Code
- Zero-install demo (just open `index.html`)

## Try it now
[Open the live demo](https://eurisko-info-lab.github.io/prismriver-live) (after enabling GitHub Pages)

## Real Prismriver integration
```lean
import Prismriver
#play ♩[c4 c4 c4 c4]  -- Boléro snare ostinato