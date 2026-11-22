#!/usr/bin/env python3
"""Make portable archive of v19 evidence and SHA256SUMS."""
from pathlib import Path
import hashlib,zipfile,json
p=Path(__file__).resolve().parent
root=p.parent
files=sorted([x for x in p.iterdir() if x.is_file() and x.name not in ('SHA256SUMS.txt',)])
sha={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in files}
(p/'SHA256SUMS.txt').write_text(''.join(f'{sha[f.name]}  {f.name}\n' for f in files))
archive=root/'ether_stationary_modes_v19_2026-11-22.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for f in sorted(p.iterdir()):
  if f.is_file():z.write(f,arcname='ether_nineteenth/'+f.name)
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None
 for name,expected in sha.items():
  b=z.read('ether_nineteenth/'+name)
  assert hashlib.sha256(b).hexdigest()==expected
print(json.dumps({'archive':str(archive),'size_bytes':archive.stat().st_size,'included_files':len(files)+1,'sha256':hashlib.sha256(archive.read_bytes()).hexdigest()},indent=2))
