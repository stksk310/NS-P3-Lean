"""Read-only publication/source integrity check; no Lean execution."""
from pathlib import Path
import hashlib
import json
import sys

root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
def need(ok, msg):
    if not ok:
        raise ValueError(msg)
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((root / 'PUBLICATION_MANIFEST.json').read_text(encoding='utf-8'))
for name, digest in manifest['files'].items():
    p = (root / name).resolve()
    need(p.is_relative_to(root) and p.is_file(), 'missing/unsafe path: ' + name)
    need(sha(p) == digest, 'hash mismatch: ' + name)
source = json.loads((root / 'docs/CURRENT_SOURCES.json').read_text(encoding='utf-8'))
need(len(source['lean_sources']) == 575, '575 authoritative Lean files')
for name, digest in (source['lean_sources'] | source['config']).items():
    need(sha(root / name) == digest, 'authoritative source mismatch: ' + name)
need(sha(root / 'manuscript/P3_PREPRINT.tex') == source['manuscript_sha256'], 'manuscript identity')
need(sha(root / 'manuscript/P3_PREPRINT.pdf') == source['pdf_sha256'], 'PDF identity')
packages = json.loads((root / 'lake-manifest.json').read_text(encoding='utf-8'))['packages']
pins = json.loads((root / 'docs/DEPENDENCY_PINS.json').read_text(encoding='utf-8'))
need(len(packages) == 9 and {p['name']:p['rev'] for p in packages} == pins, 'nine dependency pins')
print(json.dumps({'status':'PUBLICATION_INTEGRITY_PASS','files_checked':len(manifest['files']),
                  'authoritative_lean_sources':575,'dependency_pins':9,
                  'optimization':sys.flags.optimize,'new_lean_execution':False}))
