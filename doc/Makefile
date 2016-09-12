all:
	mkdir -p __build/
	cp *.bib *.cls *.lhs *.tex __build/
	cd __build/ && lhs2TeX -o main.tex main.lhs && latexmk -pdf main.tex
	ln -sf __build/main.pdf .
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1

clean:
	rm -rf __build/
	rm main.pdf
