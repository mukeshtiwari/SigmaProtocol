#!/bin/zsh
# Regenerate the coqdoc HTML in doc/html (published to GitHub Pages by
# .github/workflows/pages.yml). Run `dune build` first: coqdoc reads the
# .glob files in _build to link identifiers to their definitions.
set -e
cd "$(dirname "$0")/.."

files=($(find src -name '*.v' -not -path 'src/Fiat/*' -not -path 'src/Extraction/*' | sort | sed 's|^|_build/default/|'))

rm -rf doc/html && mkdir -p doc/html
opam exec --switch=default -- rocq doc --html --utf8 --toc --toc-depth 2 --index index_symbols \
  --title "SigmaProtocol: verified Sigma protocols and e-voting" \
  -R _build/default/src/Algebra Algebra -R _build/default/src/Utility Utility \
  -R _build/default/src/Probability Probability -R _build/default/src/Crypto Crypto \
  -R _build/default/src/Frontend Frontend -R _build/default/src/Backend Backend \
  -R _build/default/src/Examples Examples -R _build/default/src/Curve Curve \
  -R _build/default/src/Fiat Fiat \
  -d doc/html "${files[@]}" > /dev/null

# GitHub Pages serves index.html as the front page; coqdoc's entry page is toc.html.
cp doc/html/toc.html doc/html/index.html
# Serve the files as they are, without Jekyll processing.
touch doc/html/.nojekyll

echo "Generated $(ls doc/html/*.html | wc -l | tr -d ' ') HTML files in doc/html"
