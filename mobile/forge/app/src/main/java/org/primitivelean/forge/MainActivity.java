package org.primitivelean.forge;

import android.app.Activity;
import android.content.Intent;
import android.graphics.Color;
import android.os.Bundle;
import android.view.Gravity;
import android.widget.*;
import com.chaquo.python.Python;
import com.chaquo.python.PyObject;
import com.chaquo.python.android.AndroidPlatform;
import org.json.*;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

public class MainActivity extends Activity {
    private final ExecutorService worker = Executors.newSingleThreadExecutor();
    private TextView status, detail;
    private LinearLayout history;
    private ScrollView scroll;
    private EditText input;
    private Button send, explore, export;
    private PyObject engine;
    private boolean busy = true;
    private static final int EXPORT = 41;
    private static final int FG = 0xffe6e9ed, BG = 0xff12161b, MUTED = 0xff9da8b3;

    private int dp(int x) { return Math.round(x * getResources().getDisplayMetrics().density); }
    private TextView text(String s, int size, int color) {
        TextView v = new TextView(this);
        v.setText(s); v.setTextSize(size); v.setTextColor(color); return v;
    }
    private Button button(String s) {
        Button b = new Button(this); b.setText(s); b.setAllCaps(false); return b;
    }
    private void controls(boolean enable) {
        busy = !enable;
        send.setEnabled(enable); explore.setEnabled(enable); export.setEnabled(enable);
    }
    @Override public void onCreate(Bundle saved) {
        super.onCreate(saved);
        getWindow().setStatusBarColor(BG); getWindow().setNavigationBarColor(BG);
        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL); root.setPadding(dp(12),dp(8),dp(12),dp(8));
        root.setBackgroundColor(BG);
        root.setFitsSystemWindows(true);
        setContentView(root);
        root.addView(text("FORGE / DIALOGUE", 23, FG));
        status = text("初期状態を読み込み中", 12, MUTED); root.addView(status);
        LinearLayout bar = new LinearLayout(this);
        explore = button("Forge探索"); export = button("JSON出力");
        bar.addView(explore, new LinearLayout.LayoutParams(0,-2,1));
        bar.addView(export, new LinearLayout.LayoutParams(0,-2,1)); root.addView(bar);
        detail = text("端末内の演算子はLean未検証", 11, MUTED); root.addView(detail);
        scroll = new ScrollView(this);
        history = new LinearLayout(this); history.setOrientation(LinearLayout.VERTICAL);
        scroll.addView(history); root.addView(scroll,new LinearLayout.LayoutParams(-1,0,1));
        LinearLayout composer = new LinearLayout(this); composer.setGravity(Gravity.BOTTOM);
        input = new EditText(this); input.setHint("文字列を入力"); input.setTextColor(FG);
        input.setHintTextColor(MUTED); input.setMaxLines(5);
        composer.addView(input,new LinearLayout.LayoutParams(0,-2,1));
        send = button("送信"); composer.addView(send); root.addView(composer);
        controls(false);
        send.setOnClickListener(v -> {
            String msg = input.getText().toString();
            if (msg.isEmpty() || busy) return;
            if (msg.codePointCount(0,msg.length()) > 4096) { detail.setText("4096文字まで"); return; }
            controls(false); detail.setText("演算子を更新中");
            worker.submit(() -> {
                try {
                    String result = engine.callAttr("send",msg).toString();
                    runOnUiThread(() -> { if (input.getText().toString().equals(msg)) input.setText(""); render(result); controls(true); });
                } catch (Exception e) { fail(e,true); }
            });
        });
        explore.setOnClickListener(v -> {
            if (busy) return;
            controls(false); detail.setText("既存のForge探索を実行中（端末内・未証明）");
            worker.submit(() -> {
                try {
                    String result = engine.callAttr("search").toString();
                    runOnUiThread(() -> { render(result); controls(true); });
                } catch (Exception e) { fail(e,true); }
            });
        });
        export.setOnClickListener(v -> {
            Intent intent = new Intent(Intent.ACTION_CREATE_DOCUMENT);
            intent.addCategory(Intent.CATEGORY_OPENABLE);
            intent.setType("application/json"); intent.putExtra(Intent.EXTRA_TITLE,"forge-dialogue.json");
            startActivityForResult(intent,EXPORT);
        });
        worker.submit(() -> {
            try {
                if (!Python.isStarted()) Python.start(new AndroidPlatform(this));
                engine = Python.getInstance().getModule("mobile_forge");
                String snapshot;
                try (InputStream in = getAssets().open("forge-snapshot.json");
                     ByteArrayOutputStream out = new ByteArrayOutputStream()) {
                    byte[] buf = new byte[8192]; int n;
                    while ((n=in.read(buf))!=-1) out.write(buf,0,n);
                    snapshot = new String(out.toByteArray(),StandardCharsets.UTF_8);
                }
                String result = engine.callAttr("start",new File(getFilesDir(),"experiment.json").getAbsolutePath(),snapshot).toString();
                runOnUiThread(() -> { render(result); controls(true); });
            } catch (Exception e) { fail(e,false); }
        });
    }
    private void fail(Exception e, boolean recover) {
        runOnUiThread(() -> { detail.setText("エラー: "+ e.getMessage()); controls(recover); });
    }
    private void render(String value) {
        try {
            JSONObject state = new JSONObject(value);
            status.setText("対話 "+state.getInt("turn_count")+"  /  既存証明世代 "+state.getInt("certified")
                +"  /  端末演算子 "+state.getInt("local")+"/"+state.getInt("limit")
                +"  /  文字 "+state.getInt("alphabet_size"));
            JSONObject search = state.optJSONObject("last_search");
            detail.setText(search==null ? "端末内の演算子は有限検査のみ・Lean未検証" :
                "探索: "+search.optString("status")+"（端末内）");
            history.removeAllViews();
            JSONArray turns = state.getJSONArray("turns");
            if(turns.length()==0) history.addView(text("入力を重ねると演算子と対応規則が変化します。最初は意味不明な応答です。",15,MUTED));
            for(int i=0;i<turns.length();i++){
                JSONObject t=turns.getJSONObject(i);
                TextView me=text("YOU  /  "+t.getInt("turn")+"\n"+t.getString("input"),16,FG);
                me.setGravity(Gravity.END); me.setPadding(dp(8),dp(10),dp(8),dp(4));
                history.addView(me);
                TextView bot=text("FORGE\n"+t.getString("output"),18,0xffb5dbcf);
                bot.setPadding(dp(8),dp(4),dp(8),dp(3)); history.addView(bot);
                String op=t.getString("operator");
                TextView meta=text(op.substring(0,Math.min(30,op.length()))+"  ·  新規 "+t.getJSONArray("new").length()
                    +"\n"+t.getString("raw_hex"),11,MUTED);
                meta.setPadding(dp(8),0,dp(8),dp(12)); history.addView(meta);
            }
            scroll.post(() -> scroll.fullScroll(ScrollView.FOCUS_DOWN));
        } catch(Exception e){ detail.setText("表示エラー: "+e.getMessage()); }
    }
    @Override protected void onActivityResult(int req,int result,Intent data) {
        super.onActivityResult(req,result,data);
        if(req!=EXPORT || result!=RESULT_OK || data==null || data.getData()==null) return;
        controls(false);
        worker.submit(() -> {
            try {
                String json=engine.callAttr("export_state").toString();
                try(OutputStream out=getContentResolver().openOutputStream(data.getData(),"wt")){
                    if(out==null) throw new IOException("document unavailable");
                    out.write(json.getBytes(StandardCharsets.UTF_8));
                }
                runOnUiThread(() -> { detail.setText("JSON保存完了"); controls(true); });
            } catch(Exception e) { fail(e,true); }
        });
    }
    @Override protected void onDestroy(){ worker.shutdown(); super.onDestroy(); }
}
