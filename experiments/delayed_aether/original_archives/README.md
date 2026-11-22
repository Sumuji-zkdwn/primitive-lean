# 遅延硬化エーテル v1–v30 — ZIP原本の全移植

このディレクトリには、2026-11-22〜23の会話で作成した **30本のZIP原本をバイト単位で保存**している。各ZIPのGit blob SHA-1は手元の原本に対する `git hash-object` と照合済み。

- [manifest.json](manifest.json): ZIP 30本と内部ファイル623件のSHA-256・サイズ・CRC32を全件記録。
- [verify_original_archives.py](../verify_original_archives.py): 原本30本と内部623ファイルのハッシュ照合・ZIP破損検査・重複／欠落監査。
- ZIPは再圧縮・再生成をせず、当時のバイト列をそのまま移した。
- **第18回の訂正**: 当初、単独で表出したファイルがなかったため実行コード欠落と記録したが、ZIP原本には `ether_eighteenth/verify_v18.py` が存在する。
- これは元データの保全であり、既存物理学の復元やLeanによる全主張の証明を保証するものではない。

## Archive inventory

| Stage | Original ZIP (download) | Internal files | SHA-256 |
|---:|---|---:|---|
| 1 | [delayed_aether_verification_2026-11-22.zip](stage_01/delayed_aether_verification_2026-11-22.zip) | 12 | `0cdaca1dd35d0534724b52a58fbec813a1ce6ed0787fd41c71c1975e99f0f83a` |
| 2 | [ether_effective_medium_verification_v2_2026-11-22.zip](stage_02/ether_effective_medium_verification_v2_2026-11-22.zip) | 23 | `e829d7e2677edda48e11217364c237890acb7727e93cbaa41934eb4373741126` |
| 3 | [ether_delayed_hardening_v3_2026-11-22.zip](stage_03/ether_delayed_hardening_v3_2026-11-22.zip) | 24 | `26192ff68deb7cacef820945af2557f10e9647c99fe9b7b2eca069bbeb464f12` |
| 4 | [ether_delayed_hardening_v4_2026-11-22.zip](stage_04/ether_delayed_hardening_v4_2026-11-22.zip) | 34 | `3ecefb3a512807c6e126531a3e1ac070d75193744ab0b7a012edcdcda4428ea4` |
| 5 | [ether_delayed_hardening_v5_2026-11-22.zip](stage_05/ether_delayed_hardening_v5_2026-11-22.zip) | 24 | `9ec71f8eccd978d751236944019496b45a2ed5698ffc475acd96fb18ce8a0391` |
| 6 | [ether_delayed_hardening_v6_2026-11-22.zip](stage_06/ether_delayed_hardening_v6_2026-11-22.zip) | 32 | `936af7e55ee9bd8efd53fd0dd7de5d042f6ab048fbd0c316a1b6ce007ff86944` |
| 7 | [ether_delayed_hardening_v7_2026-11-22.zip](stage_07/ether_delayed_hardening_v7_2026-11-22.zip) | 18 | `9ca318305e3ba3d914081ba9c0e82a6f8d2992d564bed686cb299058ec6646f1` |
| 8 | [ether_constraint_geometry_v8_2026-11-22.zip](stage_08/ether_constraint_geometry_v8_2026-11-22.zip) | 15 | `b116e201f86579c4f15b6635c5a04ebffa3e127c0f750955d8fdc4c6fa28c4f4` |
| 9 | [ether_delayed_hardening_v9_2026-11-22.zip](stage_09/ether_delayed_hardening_v9_2026-11-22.zip) | 20 | `841629d7053daa48fb57a60d8fb6e84adde86c831efd514d8dff00c10a286493` |
| 10 | [ether_topological_memory_v10_2026-11-22.zip](stage_10/ether_topological_memory_v10_2026-11-22.zip) | 15 | `e16dfe46f818fbc04d32697810a8a7fe888e30c046969b13e752be7e3b485327` |
| 11 | [ether_local_topology_geometry_v11_2026-11-22.zip](stage_11/ether_local_topology_geometry_v11_2026-11-22.zip) | 22 | `8d223a74eb85c295a527127489870f0ed1fc5572cf4254afd100ddb0d460a954` |
| 12 | [ether_self_coupled_topology_v12_2026-11-22.zip](stage_12/ether_self_coupled_topology_v12_2026-11-22.zip) | 39 | `047268af4ce674fa14693b25ebe1ff6eb53d77e52524a70b74808d4ee7c4fa46` |
| 13 | [ether_topology_shear_v13_2026-11-22.zip](stage_13/ether_topology_shear_v13_2026-11-22.zip) | 27 | `a1a07e27f335ea89be051b5dd8d01ff7cd2498012e091be8b32dea27248cf58c` |
| 14 | [ether_exponential_metric_topology_v14_2026-11-22.zip](stage_14/ether_exponential_metric_topology_v14_2026-11-22.zip) | 17 | `89a7235e5ddbc3bf3198ea2f43470d00438ee922c5a374cae909c808346741d8` |
| 15 | [ether_ADM_constraints_v15_2026-11-22.zip](stage_15/ether_ADM_constraints_v15_2026-11-22.zip) | 24 | `a24c18b659b56dbb13bdb082994f2a8ee056513bf1c215b748434531b70e5f83` |
| 16 | [ether_covariant_topological_memory_v16_2026-11-22.zip](stage_16/ether_covariant_topological_memory_v16_2026-11-22.zip) | 15 | `90f7aa3ca8e0fbbe7b0a71e2e17f015ec695df9b60b841a24c5cf75b764314a7` |
| 17 | [ether_gravity_memory_v17_2026-11-22.zip](stage_17/ether_gravity_memory_v17_2026-11-22.zip) | 25 | `e8ea66617e4b4d9341f934929981d36841809d368807400fc7a68b150fbcc25f` |
| 18 | [ether_non_spherical_geometry_v18_2026-11-22.zip](stage_18/ether_non_spherical_geometry_v18_2026-11-22.zip) | 29 | `0509e428519cf0a8cb2336b32a74e5bb0ad70c96b406a7707566a570b082a5a8` |
| 19 | [ether_stationary_modes_v19_2026-11-22.zip](stage_19/ether_stationary_modes_v19_2026-11-22.zip) | 32 | `7546d09053fed4385c084ef44980609759954ee9bdde4b6767df521bc5a07e57` |
| 20 | [ether_spin2_source_consistency_v20_2026-11-23.zip](stage_20/ether_spin2_source_consistency_v20_2026-11-23.zip) | 19 | `fe0a0b3d66265d9fa7a61f91c38c8d4850f17ebbaf9ddec693bd3f618c525a20` |
| 21 | [ether_nonlinear_self_coupling_v21_2026-11-23.zip](stage_21/ether_nonlinear_self_coupling_v21_2026-11-23.zip) | 17 | `2dc1d75a193d1f29148937c03918f6c163f2b62f14035949e8f90f8d112c4404` |
| 22 | [ether_nonlinear_noether_v22_2026-11-23.zip](stage_22/ether_nonlinear_noether_v22_2026-11-23.zip) | 16 | `eb8ef7672d4e198f8df657f50eb8dac95aa712fd957bb85cc29f7774be5e1a59` |
| 23 | [ether_spatial_gauge_nonlinear_wave_v23_2026-11-23.zip](stage_23/ether_spatial_gauge_nonlinear_wave_v23_2026-11-23.zip) | 19 | `0f3030821c49c6448b3c52fa888209c5a0d2e35951b1934a15f37c0890ee4092` |
| 24 | [ether_hypersurface_memory_v24_2026-11-23.zip](stage_24/ether_hypersurface_memory_v24_2026-11-23.zip) | 15 | `bb7c5509a44c5ff491a9588068eaf6853f7c541e53fed1da69baaf3d7d4b8db7` |
| 25 | [ether_canonical_memory_constraints_v25_2026-11-23.zip](stage_25/ether_canonical_memory_constraints_v25_2026-11-23.zip) | 15 | `577ed4085ab55d5909c5b90b28e8290bf9332752d19d2363c0c361e3651a919b` |
| 26 | [ether_covariant_memory_momenta_v26_2026-11-23.zip](stage_26/ether_covariant_memory_momenta_v26_2026-11-23.zip) | 13 | `69e890b0ef8e514bfc7ca96225ef2f77d601df258720f8af3de9ebbfcc2c3d30` |
| 27 | [ether_spatial_scalar_tensor_brackets_v27_2026-11-23.zip](stage_27/ether_spatial_scalar_tensor_brackets_v27_2026-11-23.zip) | 13 | `00505cadb033d73b6f33638f336e1bf471dac70c90d671aa6f884ff2703012b8` |
| 28 | [ether_nondiagonal_memory_gravity_v28_2026-11-23.zip](stage_28/ether_nondiagonal_memory_gravity_v28_2026-11-23.zip) | 21 | `46aaa6bd23338acd8cb1716bbeb9fbd25069cb32b1f31c0d8f2eb4b3f75eeeb9` |
| 29 | [ether_edge_distance_constraint_v29_2026-11-23.zip](stage_29/ether_edge_distance_constraint_v29_2026-11-23.zip) | 16 | `952cb0591fbf1c5556b7ff39d38c7e15c0f571e3572c910381f998340968fd81` |
| 30 | [ether_regge_gauge_memory_v30_2026-11-23.zip](stage_30/ether_regge_gauge_memory_v30_2026-11-23.zip) | 12 | `854b221cc7290caa2a4df00f3596383aeac23d3e56be61d20f351b41c6eb75cb` |

ZIP合計 **13,238,705 bytes**。内部623ファイルすべての実体が各ZIPに含まれる。

### Reproduction

```bash
python -B -X utf8 experiments/delayed_aether/verify_original_archives.py
```

このコマンドは原本保全・バイト整合性だけを検査する。各段階のPython実験の再実行や物理学的検証は別途必要。


## 追加の単独成果物18件（原本ZIP非包含／異バイト版）
[補助アーカイブ](supplemental/README.md)には、元ZIPに存在しない途中計算CSVや元ZIPとは別のプレビュー画像を保全した。全30本の原本ZIPを上書きせず、別のSHA-256台帳とCIで監査する。

原本30 ZIPの内部623件と、別保全した補助18件の合計は**641件のファイル・バリアント**である。これは30本のZIP内に641件あるという意味ではない。
