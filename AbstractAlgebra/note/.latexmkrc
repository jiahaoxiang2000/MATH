# .latexmkrc configuration for abstractAlgeNote.tex

# Set the default output format to PDF
$pdf_mode = 1;

# Use XeLaTeX for compilation (since you're using the elegantbook class)
$pdflatex = 'pdflatex %O %S';

# Enable synctex for forward and inverse search
$pdf_previewer = 'open -a Preview';  # For macOS, adjust for other OS
$synctex = 1;

# Clean up auxiliary files after compilation
$clean_full_ext = 'dvi aux bbl bcf blg fdb_latexmk fls idx ilg ind lof log lot out run.xml toc synctex.gz';

# Automatically run biber if needed (though you don't seem to be using it)
# $biber = 'biber %O %S';

# Ensure that the document is compiled enough times to resolve references
# $max_repeat = 3;