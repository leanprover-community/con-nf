# Run from the con-nf root folder.
latexmk -shell-escape -pdf --xelatex -file-line-error -halt-on-error -interaction=nonstopmode -cd -output-directory=build blueprint/src/foa_discussion.tex
