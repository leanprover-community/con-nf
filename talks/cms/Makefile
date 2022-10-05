tex:
	latexmk -shell-escape -pdflatex=xelatex -pdf -file-line-error -halt-on-error -interaction=nonstopmode -cd -output-directory=build ./presentation.tex

present:
	pympress build/presentation.pdf
