"""Document checks only: not a verification of research claims or data."""
from pathlib import Path
import re
import pymupdf

HERE = Path(__file__).resolve().parent
log = (HERE/'build/main.log').read_text(errors='replace')
bad = [x for x in log.splitlines() if re.search(
    r'undefined|Overfull \\[hv]box|Missing character|Token not allowed in a PDF string|^!|multiply defined', x, re.I)]
if bad:
    raise SystemExit('Document warnings requiring attention:\n'+'\n'.join(bad))
doc = pymupdf.open(HERE/'build/main.pdf')
text='\n'.join(p.get_text() for p in doc)
assert len(doc)>15, 'Unexpectedly short manuscript'
assert len(text)>35000, 'Unexpectedly little extractable text'
assert '\ufffd' not in text, 'Replacement characters in PDF text'
assert len(doc.get_toc())>=20, 'Missing PDF navigation'
assert not re.search(r'\b(?:TODO|TBD|FIXME)\b',text), 'Unfinished text'
(HERE/'build/main.txt').write_text(text)
print(f'Checked {len(doc)} pages, {len(doc.get_toc())} bookmarks, '
      f'{len(text.split()):,} extracted words; no unresolved citations or overfull boxes.')
