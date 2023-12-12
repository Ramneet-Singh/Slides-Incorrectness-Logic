all: pdf tex

pdf:
	pandoc --standalone --slide-level=2 --highlight-style=breezedark  --read=markdown --write=beamer slides.md -o slides.pdf

tex:
	pandoc --standalone --slide-level=2 --highlight-style=breezedark  --read=markdown --write=beamer slides.md -o slides.tex
