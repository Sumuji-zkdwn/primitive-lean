"""Append the Research passages used to assess direct consequences of the core.

Existing captures are retained. Run only when collecting source passages;
ordinary builds and verification use the saved excerpts.
"""
from pathlib import Path
import hashlib, json

ROOT=Path(__file__).resolve().parents[1]
RESEARCH=Path(r'C:\Users\Dalcia\Research\05_Notes')
SPECS=[
 ('abstract_elastica_reference_2026-10-19/combo_forgetting_2026-10-19/一般コンボと忘却の導出.md',[(270,282),(292,323)],
  '採用: 曲率からの再構成、接合に必要な位置と接線、共通継ぎ口。現在の滑らかな曲線と積分の定義で再証明する。一般の忘却・内部変数の消去は採用しない。'),
 ('recent_discussions_2026-10-19/議論の整理.md',[(199,231)],
  '採用: 直列接合における費用加法性を現在の積分から導く。指数重み、経路の和、Bellman最適化は追加の選択なので導入しない。'),
 ('abstract_elastica_reference_2026-10-19/hysteresis_interpretations_2026-10-19/FORMALIZATION.txt',[(144,170)],
  '採用: 二階微分と極値・履歴を区別する問い。一般の曲線汎関数の第二変分は今回の新規導出。四次密度、内部変数、Galois群、枝選択は採用しない。'),
 ('abstract_elastica_reference_2026-10-19/variable_pairs_2026-10-20/二変数の選び方の比較.md',[(1,27)],
  '採用境界の確認: 特定の二変数多項式と係数の選択を前提とするため、現在の一般密度からの帰結には含めない。'),
 ('abstract_elastica_reference_2026-10-19/power_log_bridge_2026-10-20/べき対数とEの簡約.md',[(1,19),(55,81)],
  '採用境界の確認: べき・対数による座標選択と特定Eを前提とする。現在の曲線エネルギーから一意に選ばれる操作ではない。'),
]

def main():
    path=ROOT/'sources/provenance.json'; data=json.loads(path.read_text('utf-8'))
    records=data['research']
    for rel,ranges,role in SPECS:
        source=RESEARCH/rel; raw=source.read_bytes()
        digest=hashlib.sha256(raw).hexdigest()
        old=next((r for r in records if r['source']==str(source)),None)
        if old:
            assert old['source_sha256']==digest, 'Source changed: '+str(source)
            continue
        lines=raw.decode('utf-8-sig').splitlines()
        assert all(1<=a<=b<=len(lines) for a,b in ranges)
        target=ROOT/'sources'/f'research_{len(records)+1:02d}.txt'
        assert not target.exists()
        excerpt='\n\n'.join('\n'.join(f'{i}: {lines[i-1]}' for i in range(a,b+1)) for a,b in ranges)
        target.write_text(f'原本: {source}\n採用用途: {role}\n\n{excerpt}\n',encoding='utf-8')
        records.append(dict(source=str(source),source_sha256=digest,line_ranges=ranges,
            excerpt=target.relative_to(ROOT).as_posix(),
            excerpt_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),role=role))
    path.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(f'{len(records)} total source records; originals unchanged.')

if __name__=='__main__':main()
