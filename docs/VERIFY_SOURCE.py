"""Verify immutable project source/API; no Lean execution, safe with python -O."""
from pathlib import Path
import sys,json,hashlib,re
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
root=Path(sys.argv[1] if len(sys.argv)>1 else '.').resolve()
raw=(root/'docs/SOURCE_MANIFEST.sha256').read_bytes()
need(sha(raw)=='0a415b291f0c949651de72af2cf3f9dcffca8444b890b7131ee7577c1b649073','manifest authority')
rows=[s.split('  ',1) for s in raw.decode().splitlines()];files={n:h for h,n in rows};need(len(files)==len(rows)==472,'472 source files')
for n,h in files.items():need(sha((root/n).read_bytes())==h,'source '+n)
pins=json.loads((root/'docs/DEPENDENCY_PINS.json').read_text())
need(len(pins)==9 and {p['name']:p['rev'] for p in json.loads((root/'lake-manifest.json').read_text())['packages']}==pins,'nine pins')
mapping=json.loads((root/'docs/PROOF_TO_LEAN_MAP.json').read_text());refs=0
for row in mapping:
 for ref in row['source']:
  b=(root/ref['path']).read_bytes();text='\n'.join(b.decode('utf-8-sig').splitlines()[ref['line']-1:]);head=ref['statement'].replace('\r\n','\n')
  need(sha(b)==ref['sourceSha256'] and text.startswith(head) and re.match(r'\s*:=',text[len(head):]),'source API');refs+=1
need(len(mapping)==69 and refs==325,'69 results/325 references')
print(json.dumps(dict(status='FROZEN_SOURCE_API_PASS',optimization=sys.flags.optimize,sourceFiles=472,leanFiles=sum(n.endswith('.lean') for n in files),pins=9,results=69,references=refs,newLeanExecution=False)))
