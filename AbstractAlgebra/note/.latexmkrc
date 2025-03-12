# LaTeX build configuration file

# Set the default build mode to PDF
$pdf_mode = 1;  # 1 = PDFLaTeX

# File patterns to clean up when running latexmk -c or -C
$clean_ext = 'run.xml toc log aux out blg bbl xdv fdb_latexmk fls';

# Always try to create PDF file
$pdflatex = 'pdflatex -synctex=1 -interaction=nonstopmode %O %S';


# Always process bibliography files when necessary
$bibtex_use = 2;

# Ensure output is verbose enough to diagnose problems
$silent = 0;
$verbose = 1;

# Disable the option that applies @default_files
$do_cd = 0;

# Set the main filename (without extension)
@default_files = ('abstractAlgeNote');
