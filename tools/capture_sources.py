"""Select research excerpts without changing the originals."""
from pathlib import Path
import hashlib, json, shutil

ROOT = Path(__file__).resolve().parents[1]
RESEARCH = Path(r'C:\Users\Dalcia\Research\05_Notes')
SPECS = [
 ('primitive_operations_2026-10-20/原始の操作と忘却の導出.md', [(1,22),(133,200),(420,432)], '命名と助手による模型、操作と観測の参照。曲線エネルギーの定義には採用しない。'),
 ('recent_discussions_2026-10-19/sources/ブラウザ回収メモ.md', [(5,38)], '古典エラスティカ記法への要求と、曲線・密度・汎関数の既存表記。'),
 ('abstract_elastica_reference_2026-10-19/classical_combo_2026-10-19/古典的な事実による構成.md', [(253,307)], '二次密度の条件付き簡約、幾何的拘束、静的消去と運動の違い。'),
 ('abstract_elastica_reference_2026-10-19/抽象エラスティカ.md', [(69,86)], '具体的四次密度は追加模型であり、エネルギーだけで更新法則は決まらない。'),
]
records=[]
for n,(relative,ranges,role) in enumerate(SPECS,1):
    src=RESEARCH/relative
    data=src.read_bytes(); lines=data.decode('utf-8-sig').splitlines()
    target=ROOT/'sources'/f'research_{n:02d}.txt'
    excerpt='\n\n'.join('\n'.join(f'{i}: {lines[i-1]}' for i in range(a,min(b,len(lines))+1)) for a,b in ranges)
    target.write_text(f'原本: {src}\n採用用途: {role}\n\n{excerpt}\n',encoding='utf-8')
    records.append(dict(source=str(src),source_sha256=hashlib.sha256(data).hexdigest(),line_ranges=ranges,excerpt=target.relative_to(ROOT).as_posix(),excerpt_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),role=role))

vendor=ROOT/'vendor'; vendor.mkdir(exist_ok=True)
md=RESEARCH/'abstract_elastica_reference_2026-10-19'/'vendor'
for name in ('markdown','markdown-3.11.1.dist-info'):
    shutil.copytree(md/name,vendor/name,dirs_exist_ok=True,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
katex=RESEARCH/'recent_discussions_2026-10-19'/'vendor'/'katex'
shutil.copytree(katex,vendor/'katex',dirs_exist_ok=True)
licenses=[str(p.relative_to(ROOT)).replace('\\','/') for p in vendor.rglob('*') if p.is_file() and 'license' in p.name.lower()]
existing=ROOT/'sources'/'provenance.json'
if existing.exists():
    captured={record['source'] for record in records}
    records.extend(record for record in json.loads(existing.read_text('utf-8'))['research']
                   if record['source'] not in captured)
(ROOT/'sources'/'provenance.json').write_text(json.dumps(dict(research=records,vendor_sources=[str(md),str(katex)],licenses=licenses,external=[
 {'title':'Euler Methodus E65, Appendix I','url':'https://scholarlycommons.pacific.edu/euler-works/65/','role':'古典的な変分問題の原典参照。今回の一般密度全体を歴史的に帰属させない。'},
 {'title':'mathlib pinned source','url':'https://github.com/leanprover-community/mathlib4/tree/5450b53e5ddc75d46418fabb605edbf36bd0beb6','role':'解析・線形代数・積分の機械証明ライブラリ。'}]),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(f'Captured {len(records)} source excerpts and rendering libraries.')
