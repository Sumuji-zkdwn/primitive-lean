package org.primitivelean.forgecore;

import android.app.Activity;
import android.content.Intent;
import android.net.Uri;
import android.os.Bundle;
import android.graphics.Color;
import android.webkit.*;
import android.widget.Toast;
import java.io.*;
import java.nio.charset.StandardCharsets;

public final class MainActivity extends Activity {
    private static final int IMPORT = 31, EXPORT = 32, LIMIT = 2_000_000;
    private WebView web;
    private ValueCallback<Uri[]> chooser;
    private String pending;
    @Override public void onCreate(Bundle saved) {
        super.onCreate(saved);
        getWindow().setStatusBarColor(0xff111518);
        getWindow().setNavigationBarColor(0xff111518);
        web = new WebView(this);
        web.setBackgroundColor(0xff111518);
        WebSettings s = web.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);
        s.setAllowFileAccess(false);
        s.setAllowContentAccess(true);
        s.setBlockNetworkLoads(true);
        s.setJavaScriptCanOpenWindowsAutomatically(false);
        web.setWebViewClient(new WebViewClient() {
            @Override public boolean shouldOverrideUrlLoading(WebView v, WebResourceRequest r) { return true; }
            @Override public WebResourceResponse shouldInterceptRequest(WebView v, WebResourceRequest r) {
                String scheme = r.getUrl().getScheme();
                if ("http".equals(scheme) || "https".equals(scheme)) {
                    return new WebResourceResponse("text/plain","UTF-8",new ByteArrayInputStream(new byte[0]));
                }
                return null;
            }
        });
        web.setWebChromeClient(new WebChromeClient() {
            @Override public boolean onShowFileChooser(WebView v, ValueCallback<Uri[]> cb, FileChooserParams params) {
                if (chooser != null) chooser.onReceiveValue(null);
                chooser = cb;
                Intent i = new Intent(Intent.ACTION_OPEN_DOCUMENT);
                i.setType("application/json"); i.addCategory(Intent.CATEGORY_OPENABLE);
                try { startActivityForResult(i, IMPORT); } catch (Exception e) { chooser.onReceiveValue(null); chooser=null; }
                return true;
            }
        });
        web.addJavascriptInterface(new Bridge(), "ForgeAndroid");
        setContentView(web);
        try (InputStream in = getAssets().open("index.html"); ByteArrayOutputStream b = new ByteArrayOutputStream()) {
            byte[] buf=new byte[8192]; int n; while ((n=in.read(buf))!=-1) b.write(buf,0,n);
            web.loadDataWithBaseURL("https://forge.local/",b.toString("UTF-8"),"text/html","UTF-8",null);
        } catch (IOException e) { Toast.makeText(this,"読み込み失敗",Toast.LENGTH_LONG).show(); }
    }
    private final class Bridge {
        @JavascriptInterface public void exportJson(String json) {
            if (json == null || json.getBytes(StandardCharsets.UTF_8).length > LIMIT) return;
            runOnUiThread(() -> {
                if (pending != null) return;
                pending = json;
                Intent i = new Intent(Intent.ACTION_CREATE_DOCUMENT);
                i.setType("application/json"); i.addCategory(Intent.CATEGORY_OPENABLE);
                i.putExtra(Intent.EXTRA_TITLE,"forge-core.json");
                try { startActivityForResult(i, EXPORT); } catch (Exception e) { pending=null; }
            });
        }
    }
    @Override protected void onActivityResult(int request,int result,Intent data) {
        super.onActivityResult(request,result,data);
        if (request==IMPORT) {
            ValueCallback<Uri[]> cb=chooser; chooser=null;
            if (cb!=null) cb.onReceiveValue(result==RESULT_OK && data!=null && data.getData()!=null ? new Uri[]{data.getData()}:null);
        } else if (request==EXPORT) {
            String json=pending; pending=null;
            if (json==null || result!=RESULT_OK || data==null || data.getData()==null) return;
            try (OutputStream out=getContentResolver().openOutputStream(data.getData(),"w")) {
                if(out==null) throw new IOException("no stream");
                out.write(json.getBytes(StandardCharsets.UTF_8));
                Toast.makeText(this,"保存しました",Toast.LENGTH_SHORT).show();
            } catch (IOException e) { Toast.makeText(this,"保存失敗",Toast.LENGTH_LONG).show(); }
        }
    }
    @Override protected void onDestroy() { if(chooser!=null) chooser.onReceiveValue(null); if(web!=null){web.removeJavascriptInterface("ForgeAndroid");web.destroy();} super.onDestroy(); }
}
