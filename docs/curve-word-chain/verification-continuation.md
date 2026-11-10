# 曲線文字チェイン追補の検証

解析・最適化追補の共通検証結果を記録するファイル。個別のLean probeは成功しているが、この実装スナップショットに対する共通組立・全宣言監査の結果は検証実行後に追記する。第一段階の成功を今回の成功として扱わない。

実行入口は `python -B -X utf8 tools/verify.py --integration-only`。今回の原稿・宣言・SHA-256は [continuation-provenance.json](continuation-provenance.json)、形式化の範囲は [continuation.md](continuation.md) に対応する。
