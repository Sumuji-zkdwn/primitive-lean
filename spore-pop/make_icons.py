from PIL import Image, ImageDraw, ImageFilter, ImageFont
from pathlib import Path
import math,random
r=Path(__file__).parent
random.seed(32)

def make_icon(N):
    k=N/512
    im=Image.new('RGB',(N,N),(6,22,29));px=im.load()
    for y in range(N):
        for x in range(N):
            dx=(x-N*.5)/(N*.66);dy=(y-N*.48)/(N*.62)
            g=max(0,1-math.sqrt(dx*dx+dy*dy))
            px[x,y]=(int(7+19*g),int(19+36*g),int(28+35*g))
    glow=Image.new('RGBA',(N,N),(0,0,0,0))
    d=ImageDraw.Draw(glow)
    def orb(cx,cy,rad,color):
        x=int(cx*k);y=int(cy*k);rr=rad*k
        R,G,B=color
        for j in range(int(rr*2.1),0,-1):
            q=j/max(1,rr*2.1)
            c=(R,G,B,int(30*(1-q)**1.2))
            d.ellipse([x-j,y-j,x+j,y+j],fill=c)
        d.ellipse((x-rr,y-rr,x+rr,y+rr),fill=(R,G,B,255),outline=(237,255,247,190),width=max(1,int(4*k)))
        for j in range(8):
            a=j*2*math.pi/8
            rr2=rr*.85
            dr=4*k
            xx=x+math.cos(a)*rr2;yy=y+math.sin(a)*rr2
            d.ellipse([xx-dr,yy-dr,xx+dr,yy+dr],fill=(R,G,B,190))
        d.ellipse([x-rr*.52,y-rr*.55,x-rr*.03,y-rr*.06],fill=(244,255,247,230))
        d.ellipse([x+rr*.24,y+rr*.23,x+rr*.42,y+rr*.41],fill=(240,255,243,145))
    orb(203,247,108,(96,218,176))
    orb(361,333,73,(247,119,177))
    orb(348,122,48,(249,212,119))
    im=Image.alpha_composite(im.convert('RGBA'),glow.filter(ImageFilter.GaussianBlur(max(1,int(1.1*k)))))
    d=ImageDraw.Draw(im)
    for j in range(10):
        a=j*math.pi*2/10
        x=258+180*math.cos(a);y=240+170*math.sin(a)
        rr=(1.2+j%3)*k
        d.ellipse([x*k-rr,y*k-rr,x*k+rr,y*k+rr],fill=(196,255,226,205))
    return im.convert('RGB')

for N in (180,192,512):
    im=make_icon(N)
    im.save(r/'Web'/'icons'/f'{N}.png',optimize=True)
    if N==512: im.save(r/'ios'/'SporePop'/'Assets.xcassets'/'AppIcon.appiconset'/'AppIcon.png',optimize=True)
print('Generated app icons')
