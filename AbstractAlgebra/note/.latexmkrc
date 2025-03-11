# LaTeX build configuration file

# Set the default build mode to PDF
$pdf_mode = 5;  # 5 = XeLaTeX

# Use XeLaTeX for compilation
$xelatex = 'xelatex -synctex=1 -interaction=nonstopmode %O %S';

# File patterns to clean up when running latexmk -c or -C
$clean_ext = 'run.xml toc log aux out blg bbl xdv fdb_latexmk fls';

# Always try to create PDF file
$pdflatex = 'pdflatex -synctex=1 -interaction=nonstopmode %O %S';

# View the generated PDF with the system's default PDF viewer
$pdf_previewer = 'open %O %S';

# Always process bibliography files when necessary
$bibtex_use = 2;

# Ensure output is verbose enough to diagnose problems
$silent = 0;
$verbose = 1;

# Disable the option that applies @default_files
$do_cd = 0;

# Set the main filename (without extension)
@default_files = ('abstractAlgeNote');
