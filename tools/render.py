"""Build static, offline, accessible HTML with real typeset mathematics."""
from pathlib import Path
import html, json, re, subprocess, sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'vendor'))
import markdown

CSS='''
:root{color-scheme:light;--ink:#233c3b;--muted:#647575;--line:#d4dfda;--accent:#246859}
*{box-sizing:border-box}body{margin:0;color:var(--ink);background:#f5f5ef;font:16px/1.95 "Yu Gothic UI","Yu Gothic",Meiryo,sans-serif}
a{color:var(--accent);text-underline-offset:.2em;overflow-wrap:anywhere}a:focus-visible{outline:3px solid #b97a30;outline-offset:4px}
header{background:#e9efea;padding:14px max(20px,calc((100vw - 1280px)/2));border-bottom:1px solid var(--line)}header a{margin-right:22px}
.layout{display:grid;grid-template-columns:235px minmax(0,1fr);max-width:1280px;margin:28px auto;gap:30px;padding:0 20px}
aside{position:sticky;top:18px;max-height:92vh;overflow:auto;align-self:start;font-size:13px;background:#fff;border:1px solid var(--line);border-radius:10px;padding:16px}aside ul{padding-left:19px}
main{min-width:0;background:white;border:1px solid var(--line);border-radius:12px;padding:36px 42px}h1{font-size:29px;line-height:1.55;margin-top:0}h2{font-size:23px;margin-top:2.3em;border-top:1px solid var(--line);padding-top:1em;scroll-margin-top:20px}h3{font-size:18px;margin-top:1.8em}
p,li,td{overflow-wrap:anywhere}.math-display{overflow-x:auto;overflow-y:hidden;padding:8px 4px;margin:16px 0}.katex-display{margin:0!important}.katex{font-size:1.08em!important}
.katex-display>.katex{display:inline-block;min-width:100%}.katex-display>.katex>.katex-html>.tag{position:static;margin-left:2em}
.table-scroll{overflow:auto;margin:22px 0;border:1px solid var(--line);border-radius:6px}table{border-collapse:collapse;width:100%;font-size:14px;line-height:1.7}th,td{padding:11px 12px;text-align:left;vertical-align:top;border-bottom:1px solid var(--line);min-width:110px}th{background:#edf3ef}
code{font: .9em Consolas,monospace;background:#edf2ef;padding:2px 4px}pre{white-space:pre-wrap;overflow-wrap:anywhere;background:#edf2ef;padding:16px;border-radius:6px}pre code{padding:0}blockquote{border-left:4px solid #669b87;margin:20px 0;padding:4px 18px;background:#f1f6f3}
footer{padding:15px 20px 40px;text-align:center;color:var(--muted);font-size:13px}.skip{position:absolute;top:-80px}.skip:focus{top:4px;background:white;padding:8px}
@media(max-width:800px){.layout{display:block;padding:0 12px;margin-top:14px}aside{position:static;max-height:200px;margin-bottom:16px}main{padding:24px 18px}h1{font-size:25px}h2{font-size:21px}}
@media print{header,aside,footer,.skip{display:none}.layout{display:block;margin:0;padding:0}main{border:0;padding:0}.math-display{overflow:visible}h2,h3{break-after:avoid}}
'''

def build():
    outputs=[]
    for name in ('原始の形式化.md','検証と再実行.md','linear_input/線形入力の使い方.md'):
        path=ROOT/name
        raw=path.read_text('utf-8')
        expressions=[]
        def protect(m):
            display=m.group(1) is not None
            tex=m.group(1) if display else m.group(2)
            index=len(expressions); expressions.append(dict(tex=tex,display=display))
            token=f'MATHPLACEHOLDER{index:05d}END'
            return '\n\n'+token+'\n\n' if display else token
        marked=re.sub(r'\\\[(.*?)\\\]|\\\((.*?)\\\)',protect,raw,flags=re.S)
        result=subprocess.run(['node',str(ROOT/'tools'/'render_math.cjs')],input=json.dumps(expressions),encoding='utf-8',capture_output=True,check=True)
        rendered=json.loads(result.stdout)
        md=markdown.Markdown(extensions=['tables','fenced_code','toc','sane_lists'],extension_configs={'toc':{'toc_depth':'2-3'}})
        body=md.convert(marked)
        toc=md.toc
        for i,math in enumerate(rendered):
            token=f'MATHPLACEHOLDER{i:05d}END'
            # A heading may also appear in the TOC. Use its source notation as
            # a plain label there; the heading itself gets full math typesetting.
            toc=toc.replace(token,html.escape(expressions[i]['tex']))
            if expressions[i]['display']:
                body=body.replace('<p>'+token+'</p>','<div class="math-display" tabindex="0">'+math+'</div>')
            else: body=body.replace(token,math)
        body=body.replace('<table>','<div class="table-scroll" tabindex="0"><table>').replace('</table>','</table></div>')
        title=raw.splitlines()[0].lstrip('# ').strip()
        output=path.with_suffix('.html')
        prefix='../' if path.parent!=ROOT else ''
        source_name=path.name
        output.write_text(f'''<!doctype html><html lang="ja"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="color-scheme" content="light"><title>{html.escape(title)}</title><link rel="stylesheet" href="{prefix}vendor/katex/katex.min.css"><style>{CSS}</style></head><body><a class="skip" href="#content">本文へ</a><header><a href="{prefix}原始の形式化.html">原始の形式化</a><a href="{prefix}検証と再実行.html">検証と再実行</a><a href="{prefix}sources/provenance.json">出典</a><a href="{prefix}linear_input/explore.html">線形入力の操作</a></header><div class="layout"><aside aria-label="目次"><strong>目次</strong>{toc}</aside><main id="content">{body}</main></div><footer>曲線の変分・線形入力・帰還系 · <a href="{html.escape(source_name)}">編集原稿</a> · 数式とフォントはローカル収録</footer></body></html>''',encoding='utf-8')
        outputs.append(dict(file=output.relative_to(ROOT).as_posix(),math_expressions=len(expressions)))
    (ROOT/'verification'/'render.json').write_text(json.dumps(outputs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    former_reader=next(record for record in outputs if record['file']=='linear_input/線形入力の使い方.html')
    (ROOT/'linear_input'/'render.json').write_text(json.dumps(dict(
        file='線形入力の使い方.html',math_expressions=former_reader['math_expressions'],
        unified_report='../verification/render.json',
        scope='Former reader is a navigation page; the complete mathematical text is in the unified root reader.'
    ),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(outputs,ensure_ascii=False))
if __name__=='__main__':build()
