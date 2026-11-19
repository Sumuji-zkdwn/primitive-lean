# Rulefold — Higher-order self-extension playground

A **single HTML file** that simulates the precise `Fin 4` witness of [PR #73](https://github.com/Sumuji-zkdwn/primitive-lean/pull/73), including the frozen-meta control.

Open `higher_order_playground.html` in any modern browser. No server or build step is required. Use **1ステップ進める** to inspect transitions, **終点まで実行** to reach finite saturation, toggle viability/edit conditions to test counterfactuals, and **履歴をJSON保存** to export the trace.

Optional zero-dependency regression check:

```sh
node --test demos/higher_order_playground.test.cjs
```

## Exact correspondence

The HTML engine mirrors the `HigherMachine` fields `known`, `edges`, `metaRules`, `liftRules`, `liftEdits`, and the ordering in `higherStep`: select first viable frontier target; apply lift edits; use resulting lift rules to emit meta rules; **use old meta rules** to emit object edges. Initial state:

```
known     = [0]
edges     = [(0,1)]
metaRules = [(1,(1,2))]
liftRules = []
liftEdits = [(1,(1,(2,(2,3))))]   // mutable case only
```

The two outcomes have distinct known-operator catalogs, exactly as the Lean witness: mutable `[0,1,2,3]`, frozen `[0,1,2]`. The observation-class count here equals the number of distinct one-step child lists of known operators, yielding 4 and 3 respectively for this finite experiment.

This independent JavaScript model is **not automatically a Lean proof** and is not an unbounded self-improving system. It is an executable reference visualization of the already formalized finite witness. Changes to the source `HigherOrderLiftSelfRewriting.inc` must be checked against the JavaScript tests and behavior before claiming continued parity. The UI does not modify source files or GitHub branches.

## 曲線の双子を探す

[デモを開く](curve_word_twins.html)。[曲線文字の整数模型](../docs/curve-word-chain/README.md)で A と B を各 4〜6 個並べ、終点と符号付き面積が一致する語を見比べる。スライダーは両方の曲線を同じ文字数まで描く。左右の座標軸・縮尺は共通。

ブラウザで全列挙した分類を `tools/check_curve_word_chain.py` の `state` と照合した。各 4 個では 70 語が 50 組、各 5 個では 252 語が 118 組、各 6 個では 924 語が 242 組になる。これは指定した語長での有限計算である。
