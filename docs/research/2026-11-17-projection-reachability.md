# 射影・操作模倣・到達域の真の拡大

2026-11-17（日本時間）。PR #145のヘッド `c0fbb2221c1df138d7c094c61996e21772e894ff` に積み重ねる追加。旧PRのブランチやmainは更新しない。
新しい証明断片、独立有限検算、統一検証入口、専用CIを追加する。

検証結果: **PASS**。Lean `--trust=0`、公理監査、Python全探索、
Lean/Pythonの288遷移照合が成功。詳細は `verification/projection-reachability/verification.json` を参照。

## 出典と今回の追加

- PR #145: https://github.com/Sumuji-zkdwn/primitive-lean/pull/145
- 固定したソースヘッド: `c0fbb2221c1df138d7c094c61996e21772e894ff`
- `OperatorReachability.inc` の既存 `Reachable`、`reachable_trans`、不変量補題を直接再利用。
- PR #145 の `Allowed`、`run`、`RevenuePossible`、`Blocks` を直接再利用。
- 既存ファイルを同名の再実装に差し替えていない。既存証明本文を直接読み、使用した全入力のSHA-256を検証結果に記録する。
- 参照時のmainにある `OperatorReachability.inc` も同じblob
  `bba89d0e48ec3614a621767983054f7820e13c9c` だった。

この追加候補はPR #145に既存の定理ではなく、本検証で構成したもの。
以下は有限語到達性・前向き模倣に関する初等的な結果であり、一般数学上の新規性は主張しない。

## 1. 射影による模倣と保存

旧操作 `old : I → X → X`、新操作 `fresh : J → Y → Y`、射影 `π : Y → X` を固定する。
`Reachable` は空語を含む有限操作列での到達可能性。

```text
ProjectionSimulation old fresh π :=
  ∀ j y, Reachable old (π y) (π (fresh j y))
```

つまり、新しい各一手は射影後、旧系の0手以上の有限列で再現できる。
量化順序は `∀ j y, ∃ word`。語が現在状態に依存してよい。
状態によらないコンパイラ `code : J → List I` の存在はこれより強い十分条件。

保存補題 `projection_reachable`:

```text
ProjectionSimulation old fresh π →
Reachable fresh y z → Reachable old (π y) (π z)
```

証明は操作列についての帰納法と既存の到達可能性の推移律。
有限性、πの全射性、単射性、逆写像、語長上限は仮定しない。
`simulation_iff_all_reachability` は、この模倣条件が**すべての出発点・終点**における
射影後の到達性保存と同値であることも示す。

`generated_projection_simulation` で、既存の操作列コンパイルを `π = id` の特例として接続した。
旧操作も残す場合の到達関係の一致は、既存の `generated_extension_reachability` をそのまま使用できる。

## 2. 初期状態を固定したとき、真に増える正確な条件

```text
StrictGain old fresh π s :=
  ∃ z, Reachable fresh s z ∧ ¬ Reachable old (π s) (π z)
```

`strictGain_iff_escape`:

```text
StrictGain old fresh π s ↔
  ∃ y j, Reachable fresh s y
       ∧ Reachable old (π s) (π y)
       ∧ ¬ Reachable old (π s) (π (fresh j y))
```

すなわち、**実行可能な新経路に、旧初期状態の到達域から初めて外へ出る一手があること**が必要十分。
一般の模倣不成立だけでは、固定初期状態からの増加は保証されない。
新操作が実行不能な場所でだけ違う場合に加え、到達域内を後戻りするだけの場合もある。

厳密な集合包含 `Reach_old ⊊ π(Reach_new)` を主張するには、旧経路を失わない条件も必要。
`old_reachable_lifts` は `embed : X → Y` と
`π (embed x) = x`、各旧一手の新有限語への持ち上げ、初期状態 `embed x₀` から
旧到達域の包含を証明する。これと `StrictGain` を合わせれば真の拡大となる。
単に新しい点が一つあるだけでは、両到達集合が包含関係にあるとは限らない。

## 3. 最小反例と比較例

| 模型 | 旧系 | 新系・射影 | 結果 |
|---|---|---|---|
| 同じ2状態 | `X = Bool`、恒等操作のみ、開始0 | `Y = X`、0を1にする操作追加、π=id | 旧 `{0}` → 新 `{0,1}` |
| 真に大きい状態空間 | `X = Bool`、恒等操作のみ、開始0 | `Y = Fin 3`、0→1→2、π=(0,0,1)、恒等操作も残す | 旧 `{0}` → 射影後 `{0,1}` |
| 余分なメモリ | 任意の旧系 | `Y=X×Bool`、旧操作を持ち上げ、追加操作はBoolだけ反転、π=fst | 新しい内部状態は増えても射影後は増えない |
| 模倣失敗でも増加しない | 旧0→1、1→1 | 1→0のリセットを追加、π=id | 1から0への模倣は失敗するが、開始0の到達域は既に `{0,1}` |

2状態例は**状態数**について最小。旧操作の文字数最小という主張ではない
（空の旧アルファベットでも同じ反例を作れる）。
`gain_has_distinct_projections` と `gain_cardinality_bounds` により、増加には異なる旧状態が二つ必要。
さらに `|Y|>|X|` を要求すると `|Y|≥3`。したがって2→3例はこの条件下で状態数最小。
2→3例では旧動作の持ち上げと射影の切断則もLeanで検証する。

## 4. PR #145の許可付き操作系との厳密な接続

許可された文字の部分型を作る:

```text
Permitted A := { a : I ⊕ G // Allowed A [a] }
permittedStep step A a := step a.val
```

`revenue_iff_reachable` は、元のPRの述語との同値を証明する:

```text
RevenuePossible step s goal A ↔
  ∃ z, Reachable (permittedStep step A) s z ∧ goal z
```

`PermissionSimulation` は旧許可集合A、新許可集合Bを明示する。
`revenue_of_permission_simulation` では新目標を `goal ∘ π` として比較する。
`blocks_of_permission_simulation` は、同じ `E \ K` で模倣が成立する限り、
旧遮断集合が新系でも遮断集合になることを示す。包含最小性の保存までは主張しない。

許可を無視して旧外部操作を内部マクロとして使うと、無断で条件を変えることになる。
比較時は許可集合を固定するか、その差を仮定として明記する必要がある。

## 5. 椅子の内部生成を具体模型に適用

PRの1チャンネル、閾値3の模型をLeanに追加した。
状態は `(capability : Fin 4, chair : Bool, demand : Bool, paid : Bool)` の32状態。
旧内部操作はgrowとsale、新内部操作はそれらとmake-chair。
無効な操作は自己ループとして全域化する。
元のPython実装は無効な辺を列挙しないが、自己ループの追加では到達域は変わらない。

Leanで全許可集合Aについて証明する:

```text
old_possible_iff : oldSuccess A ↔ chair ∈ A ∧ demand ∈ A
new_possible_iff : newSuccess A ↔ demand ∈ A
```

| 利用可能な外部条件 | 旧系 | 椅子内部生成あり |
|---|---|---|
| ∅ | 不可 | 不可 |
| {chair} | 不可 | 不可 |
| {demand} | 不可 | 可 |
| {chair,demand} | 可 | 可 |

新系で `{demand}` のみを許可した証明語は
`grow, grow, grow, make-chair, external:demand, sale` の6手。
`chair_strict_gain` と `chair_not_simulated` により、同一許可・同一状態空間で
新しい到達状態があり、許可を保つ模倣が不成立であることを証明する。
`chair_retains_old` は全許可集合・全初期状態で旧経路が残ることを証明するので、
`{demand}` での到達集合は真の包含拡大になっている。
`no_external_success` により外部条件なしでは成功しない。

外部chairが許可されている場合は `chair_simulated_when_chair_available` が成立する。
閾値未満では旧空語、閾値到達時では旧external:chairの一手でmake-chairの効果を再現できる。

**分類上の修正**: PRのPythonにあるmake-chairは既存のunlocked集合を書き換える操作であり、
状態の型や状態集合そのものを拡大していない。新しいプリミティブの追加である。
その結果、同じ外部許可集合で成功域が増え、最小外部条件が減る。
外部条件そのものの追加 `A⊆B` は別の変更で、元PRの `revenue_mono` が扱う。

## 6. 検証の範囲

機械可読の最終結果は `verification/projection-reachability/verification.json`、Lean出力は `verification/projection-reachability/lean430.log`、
独立な有限全探索結果は `verification/projection-reachability/python_results.json` に記録する。
`tools/verify_projection_reachability.py` は一つでもエラー・未許可公理・遷移不一致があれば失敗する。

- Lean: PRと同じ `4.30.0-rc2`、Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
- `--trust=0` で追加候補と必要な既存宣言をコンパイルし、35個の公開追加定理の公理を監査。
- 許容公理は `propext`, `Classical.choice`, `Quot.sound` のみ。`sorryAx` は禁止。
- Python: 旧2状態／新2状態の64系と、旧2状態／新3状態の864系を全列挙。
  それぞれ旧・新一操作を全関数から選び、全射影・全初期状態を検査。合計928系・2,720開始点。
- 椅子: 32状態×4許可集合×旧新2模型=256文脈で、独立な全域遷移表の非自己辺を元Pythonと全件照合。
- Lean自身から全288遷移を `#eval` 出力し、上の独立遷移表と照合する。
  これはプログラムの有限表の機械照合であり、Python処理系とLean処理系の意味論全体の同値定理ではない。
- PRの4模型の最小集合検査と、4入力単調ブール関数168個の検査も実行。

検証用 `ProjectionCheck.lean` では広い `import Mathlib` を必要な3 importへ絞る。
既存の宣言本文は変更しない。元のファイルはリポジトリ内の既存パスから読み込み、変更しない。
リポジトリ全体の統合CIを今回の追加候補で再実行したという主張ではない。
実装・中間確認に使用した他バージョンでの失敗を、最終合格結果に混ぜない。

## 7. CCCの自己拡張へ持ち上げるための仮定

1. 比較する観測量・目標を固定し、πで新旧の状態の意味を対応させる。
   新目標が旧目標の引き戻しでなければ、単に評価基準を変えた可能性が残る。
2. 操作生成・登録・実行・資源消費を状態と遷移に含める。
   生成されるコードや操作辞書をYの一部にすれば、動的な操作追加も固定したメタ操作系として扱える。
3. 到達可能な状態で実行され得る全操作について模倣を確保する。
   コード生成器を追加しただけでは、この仮定やその失敗は自動では得られない。
4. 初期状態の対応、旧操作の持ち上げ、固定した外部許可・資源制約を与える。
   厳密な拡大には、具体的な新経路と旧到達不能性の証明（例:旧不変量）が必要。
5. ここでの意味論は全域・決定的操作の存在的有限語到達性。
   非決定的系や部分操作には実行可能性を保持する関係的模倣が別途必要。
   「必ず成功」には外部イベントや環境に対する量化・公平性等の別仮定が必要。
6. 語長・時間・メモリ等の予算は今回のReachableに含めていない。
   到達域が同じでもコンパイルで短縮・高速化する余地がある。予算付きの主張には費用意味論が必要。

現実の需要・購入・収益化・その確率についての証明ではない。

## 8. ファイル配置と再現方法

新しい証明は `linear_input/lean_check/` に追加する。

| ファイル | 役割 |
|---|---|
| ProjectionReachability.inc | 射影模倣、保存、増加条件、旧経路の持ち上げ、最小状態数 |
| PermissionProjectionBridge.inc | PR #145の許可付き到達可能性との厳密な接続 |
| FiniteProjectionExamples.inc | 最小反例と境界例 |
| ChairInternalGeneration.inc | 32状態の椅子模型、全許可集合での成功条件、旧経路保持 |
| ChairProjectionExport.inc | 全288遷移のLean出力 |

専用検証は既存の統一入口から実行する:

```bash
python -B tools/verify.py --projection-reachability-only
```

依存キャッシュがない場合、先に `lean/` で次を実行する:

```bash
lake exe cache get Mathlib.Data.Finset.Card Mathlib.Data.Fintype.Card Mathlib.Tactic.SplitIfs
```

Pythonだけの独立全探索:

```bash
python -B tools/projection_reachability_finite.py
```

Python単独実行ではLeanログが存在しないと遷移出力照合を `NOT_RUN` と表示する。
統一入口の実行はLeanログを新しく生成し、全288遷移の照合が `PASS` であることを必須にする。

専用CI `.github/workflows/projection-reachability.yml` はPRの実際のhead SHAをチェックアウトし、
有限検算と `--trust=0` のカーネル検証を実行する。出力・組み立てたLeanソース・入力ハッシュを
Actions artifactへ保存する。この専用検証をリポジトリ全体の統合検証とは呼ばない。

ローカルの公開前検証記録は `docs/verification/projection-reachability-20261117/` に収録する。
これらはソースSHA-256に結び付くローカル記録であり、GitHub Actionsの成功通知ではない。
