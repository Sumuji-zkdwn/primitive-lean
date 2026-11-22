"""Package the condition comparison and the anonymous inputs needed to reproduce it."""
from pathlib import Path
import hashlib
import json
import shutil
import zipfile


ROOT=Path(__file__).resolve().parent.parent
HERE=Path(__file__).resolve().parent


def digest(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()


def main():
    refs=["cpr_empirical/analyze_sand.py","cpr_empirical/conditions.csv","cpr_empirical/quality_flags.csv",
          "cpr_empirical/results/round_sand.csv","cpr_redefinition/harvest_asm/summary.csv",
          "cpr_redefinition/harvest_asm/events.csv","cpr_redefinition/harvest_asm/analyze_harvest_asm.py"]
    files={ROOT/x for x in refs}
    files.update((ROOT/'cpr_redefinition/harvest_asm/trials').glob('two_*.npz'))
    files.update(p for p in HERE.rglob('*') if p.is_file())
    files=sorted(p for p in files if '__pycache__' not in p.parts and p.suffix!='.pyc' and p.name not in ['package_manifest.json','package_receipt.json'])
    assert all(p.is_file() for p in files)
    manifest={'analysis_date_jst':'2026-11-21','raw_archives_included':False,
              'external_raw_archive':{'relative_path':'cpr_empirical_sources/02_expCPR_2player(1).zip',
                                      'sha256':'536996e6a977de63fcb82e9a0678c51cded6cd3bd2e962fbfeb00701dbcb9896'},
              'files':[{'path':str(p.relative_to(ROOT)),'size_bytes':p.stat().st_size,'sha256':digest(p)} for p in files]}
    manifest_path=HERE/'package_manifest.json'
    manifest_path.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
    out=ROOT/'cpr_coop_comp_2026-11-21.zip'
    with zipfile.ZipFile(out,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for p in files+[manifest_path]:z.write(p,str(p.relative_to(ROOT)))
    with zipfile.ZipFile(out) as z:
        assert z.testzip() is None
        assert len(z.namelist())==len(files)+1
    shutil.copyfile(HERE/'README.md',ROOT/'cpr_coop_comp_2026-11-21.md')
    shutil.copyfile(HERE/'coop_comp_comparison.png',ROOT/'cpr_coop_comp_2026-11-21.png')
    receipt={'zip':out.name,'size_bytes':out.stat().st_size,'sha256':digest(out),'files':len(files)+1,'zip_integrity':'passed'}
    (HERE/'package_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
