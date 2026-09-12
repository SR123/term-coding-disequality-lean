from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
MANUSCRIPT=ROOT.parent/'MANUSCRIPT' if (ROOT.parent/'MANUSCRIPT/paper3.tex').exists() else ROOT/'paper'
PDFBUILD=ROOT/'build/paper' if (ROOT/'build/paper/paper3.pdf').exists() else ROOT.parent/'BUILD/hybrid-015'
