from pathlib import Path
r=Path(__file__).parent
html=(r/'Web/index.html').read_text(encoding='utf-8')
html=html.replace('<link rel="stylesheet" href="styles.css" />','<style>\n'+(r/'Web/styles.css').read_text(encoding='utf-8')+'\n</style>')
html=html.replace('<script src="engine.js"></script><script src="game.js"></script>', '<script>\n'+(r/'Web/engine.js').read_text(encoding='utf-8')+'\n</script>\n<script>\n'+(r/'Web/game.js').read_text(encoding='utf-8')+'\n</script>')
html=html.replace('<link rel="manifest" href="manifest.webmanifest" />','').replace('<link rel="apple-touch-icon" href="icons/180.png" />','')
html=html.replace("<script>if ('serviceWorker' in navigator && location.protocol.startsWith('http')) window.addEventListener('load',()=>navigator.serviceWorker.register('./sw.js').catch(()=>{}));</script>",'')
p=Path('/mnt/data/SPORE-POP-iPhone-Play.html')
p.write_text(html,encoding='utf-8')
print(p,p.stat().st_size)
