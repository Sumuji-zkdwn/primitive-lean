import threading,http.server,socketserver
from pathlib import Path
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[1]/'Web'
class Handler(http.server.SimpleHTTPRequestHandler):
 def __init__(self,*args,**kwargs): super().__init__(*args,directory=str(ROOT),**kwargs)
 def log_message(self,*args): pass
server=http.server.ThreadingHTTPServer(('127.0.0.1',0),Handler)
threading.Thread(target=server.serve_forever,daemon=True).start()
url=(ROOT/'index.html').as_uri()
with sync_playwright() as p:
 browser=p.chromium.launch(headless=True,executable_path='/usr/bin/chromium',args=['--no-sandbox'])
 page=browser.new_page(viewport={'width':390,'height':844},device_scale_factor=2,is_mobile=True,has_touch=True)
 errors=[]
 page.on('pageerror',lambda exc: errors.append(str(exc)))
 html=(ROOT/'index.html').read_text()
 html=html.replace('<link rel="stylesheet" href="styles.css" />','<style>'+(ROOT/'styles.css').read_text()+'</style>')
 html=html.replace('<script src="engine.js"></script><script src="game.js"></script>','<script>'+(ROOT/'engine.js').read_text()+'</script><script>'+(ROOT/'game.js').read_text()+'</script>')
 page.set_content(html,wait_until='load')
 page.screenshot(path='/mnt/data/SPORE-POP-start-preview.png')
 assert page.get_by_role('button',name='PLAY',exact=False).is_visible()
 page.click('#play')
 before=page.evaluate('window.__sporeDebug.snapshot()')
 assert before['playing'] and before['shots']==5,before
 page.screenshot(path='/mnt/data/SPORE-POP-game-preview.png')
 page.locator('canvas').tap(position={'x':180,'y':190})
 page.wait_for_timeout(1200)
 after=page.evaluate('window.__sporeDebug.snapshot()')
 assert after['shots']==4 and after['activePulses']>=0,after
 page.click('#help')
 assert page.get_by_text('連鎖させよう').is_visible()
 page.click('#resume')
 assert page.evaluate('window.__sporeDebug.snapshot().playing')
 page.click('#restart')
 assert page.evaluate('window.__sporeDebug.snapshot().shots')==5
 page.click('#help');page.click('#home');page.click('#zen')
 assert page.evaluate('window.__sporeDebug.snapshot().mode')=='zen'
 page.locator('canvas').tap(position={'x':140,'y':190})
 page.wait_for_timeout(350)
 assert not errors,errors
 print('PASS web mobile smoke: title, campaign, pointer/taps, help, restart, zen, no JS errors')
 print('STAGE before:',before,'after:',after)
 browser.close()
server.shutdown()
