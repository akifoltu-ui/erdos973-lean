# Erdős Problem #973: witnesses, checker, Lean 4 files and OpenTimestamps proofs

Software record of the paper

> M. A. Oltulu, *An equal-modulus family for Erdős Problem #973: exact values for n ≤ 6, an upper bound for every n, and the limit constant ε∞ = 0.07725484…*, version 1.0, Zenodo, 2026.
> DOI: [10.5281/zenodo.24543535](https://doi.org/10.5281/zenodo.24543535)

The paper (English and Turkish) is on Zenodo. This repository contains the files that accompany it.

## Contents

| Path | Content | Paper |
|---|---|---|
| `checker/turan973_tanik_denetci_v1.py` | 40-digit witnesses for n = 3, 4, 5, 6 and the exact rational checker | Section 5.1, Appendix B |
| `lean/TURAN973_v04/` | Lean 4: bounds for n = 21, 31, 50, 75 | Section 5.2 |
| `lean/TURAN973_v05/` | Lean 4: equal-modulus law for every n | Section 5.2 |
| `lean/TURAN973_v06_r2/` | Lean 4: `Δ*_n ≤ B` for n = 21, 31, 50, 75 (the two combined) | Section 5.2 |
| `scripts/check_lean.py` | compiles the main files and the negative controls | |
| `ots/` | the fourteen OpenTimestamps proofs | Section 6 |
| `TURAN973_muhur_tablosu_v1.txt` | record table: archive, SHA-256, size, date, Bitcoin blocks | Section 6 |
| `MANIFEST_SHA256.txt` | SHA-256 digests of all other files | |

## Witnesses and checker

The checker reads the witnesses as exact rationals and checks `z_1 = 1`, `|z_j| ≥ 1` and `|p_k| ≤ B_n` for k = 2, …, n+1. Three corrupted copies of the n = 6 data serve as negative controls. It needs only the Python 3 standard library.

```
python3 checker/turan973_tanik_denetci_v1.py
```

Expected last line (exit code 0):

```
SUMMARY: 4/4 configurations PASS, 3/3 negative controls rejected as expected
```

## Lean 4 files

Lean `leanprover/lean4:v4.36.0-rc1` and Mathlib revision `625d8914199bc567cca9b91f90e8e5afafa5ae51`, pinned in `lean-toolchain` and `lake-manifest.json`. Every file imports only `Mathlib`. The files are those of the dated records TURAN973_v04, TURAN973_v05 and TURAN973_v06_r2 (Section 6 of the paper), unchanged.

```
lake exe cache get
python3 scripts/check_lean.py
```

The script compiles each file with `lake env lean`. A main file passes when Lean reports no error and no `sorry`, and every `#print axioms` line in the file lists only `propext`, `Classical.choice` and `Quot.sound`. A negative control (a deliberately false or incomplete statement) is flagged when Lean reports an error or `sorryAx`. Expected last line:

```
SUMMARY: 9/9 main files PASS, 9/9 negative controls flagged
```

| Folder | Statement | Main files | Negative controls | Kept as recorded |
|---|---|---|---|---|
| `lean/TURAN973_v04` | bounds for n = 21, 31, 50, 75 | Turan973_N21.lean, Turan973_N31.lean, Turan973_N50.lean, Turan973_N75.lean | Kontrol_N21_bir.lean, Kontrol_N21_ice.lean, Kontrol_N21_sahte.lean, Kontrol_N21_sinir.lean | – |
| `lean/TURAN973_v05` | equal-modulus law for every n | Turan973_L2_v2.lean | Kontrol_L2_v2_sahte.lean, Kontrol_L2_v2_yanlis.lean | earlier version: Kontrol_L2_sahte.lean, Kontrol_L2_yanlis.lean, Turan973_L2.lean; auxiliary: L2_Sonda.lean, L2_Sonda_v2.lean |
| `lean/TURAN973_v06_r2` | `Δ*_n ≤ B` for n = 21, 31, 50, 75 (the two combined) | Birlesim_N21.lean, Birlesim_N31.lean, Birlesim_N50.lean, Birlesim_N75.lean | Kontrol_B21_n22.lean, Kontrol_B21_sahte.lean, Kontrol_B21_sinir.lean | – |

The workflow `.github/workflows/lean-check.yml` runs the same check on GitHub; start it from the Actions tab.

## OpenTimestamps proofs

Each file in `ots/` commits the SHA-256 digest of one encrypted archive (second column of `TURAN973_muhur_tablosu_v1.txt`) to the Bitcoin blockchain; the same table lists the block heights. With the OpenTimestamps client (https://opentimestamps.org):

```
ots info ots/ONCELIK_TURAN973_v14_kasa.7z.ots
```

## File digests

```
sha256sum -c MANIFEST_SHA256.txt
```

## Citation

Please cite the paper (DOI above). `CITATION.cff` contains the same reference.

## License

Apache License 2.0 (`LICENSE`). The paper on Zenodo is licensed CC BY 4.0.

## Türkçe

Bu depo, yukarıdaki makalenin (DOI [10.5281/zenodo.24543535](https://doi.org/10.5281/zenodo.24543535)) yazılım kaydıdır.

- `checker/`: n = 3, 4, 5, 6 için 40 haneli tanıklar ve kesin rasyonel denetçi. `python3 checker/turan973_tanik_denetci_v1.py` komutunun son satırı: `SUMMARY: 4/4 configurations PASS, 3/3 negative controls rejected as expected`.
- `lean/`: TURAN973_v04, TURAN973_v05 ve TURAN973_v06_r2 kayıtlarının Lean 4 dosyaları, değiştirilmeden (n = 21, 31, 50, 75 için üst sınırlar; her n için eşit-modül yasası; n = 21, 31, 50, 75 için `Δ*_n ≤ B` (ikisinin birleşimi)). `lake exe cache get` ve `python3 scripts/check_lean.py` komutlarının son satırı: `SUMMARY: 9/9 main files PASS, 9/9 negative controls flagged`.
- `ots/`: tarihli kayıtların on dört OpenTimestamps kanıtı. Her kanıt bir şifreli arşivin SHA-256 özetini Bitcoin blok zincirine bağlar (`TURAN973_muhur_tablosu_v1.txt`).
- `MANIFEST_SHA256.txt`: öteki bütün dosyaların SHA-256 özetleri.

Lisans: Apache 2.0. Makale (Zenodo) CC BY 4.0 lisanslıdır.
