# Asset Price Bubbles: Theory, Signals, and Traded Contracts

A single manuscript in four parts, written for a practitioner who wants the economic meaning as well as the mathematics:

1. Theory and the limits of identification.
2. Daily and intraday price-level volatility signals, simulation, calibration, and real-data evidence.
3. Rebalancing, leveraged and inverse funds, and liquidation.
4. Options, pricing conventions, and constituent attribution.

The manuscript synthesizes existing research. Its build does not run new experiments, alter the original paper, or modify lab operations.

A background section before Part I explains the relevant valuation, detection, investment, and option literature and places the contributions in that context. Additional source PDFs are retained in `sources/`; `sources/bibliography.json` records the editions consulted and overrides their bibliography metadata locally, without changing the lab registry.

## Build

From the repository root:

```bash
bash manuscript/build.sh
```

Requires `tectonic` and the repository Python environment (`pymupdf`). `MANUSCRIPT_PYTHON` can select another Python executable. Tectonic may need network access on its first run to fetch TeX packages.

Read **`build/main.pdf`**. Edit **`main.tex`** and the files in **`sections/`**. `prepare.py` generates selected tables and vector PDF figures directly from the existing experiment result files and a bibliography from the repository registry. `generated/provenance.json` records input hashes and the repository revision. `check.py` checks compilation warnings, citation resolution, PDF structure, and text extraction. The generated sources are reproducible; `build/` holds temporary products and the finished PDF.

The text's experiment numbers identify source records; the appendix maps results to claim files, experiment directories, and formalization scope. These checks validate document production and source transcription, not the original experiments or all mathematical proofs.

The draft uses one variance-exponent convention throughout: `beta = 2(p - 1)` for CEV price exponent `p`. Earlier experiment code sometimes uses half this exponent; those differences are made explicit in the text.
