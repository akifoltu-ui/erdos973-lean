import Mathlib

/-!
# TURAN973 L2 — ailenin eşit-nota yasası (her n için)

Üreten: turan973_l2_v2.py (md5 1b97d3d00bb8ec0f2bbec5921de485b7), 2026-11-07 00:15. Yalnız Mathlib'e dayanır.\nv1 → v2: N1'in ifadesinde Finset.antidiagonal yerine Finset.HasAntidiagonal.antidiagonal (bu Mathlib'de ilki başka bir şeyi adlandırıyor).

Ana teorem (`aile_esit_nota`): c 0 = 1, (m+1)·c(m+1) = r·c(m) − ε·Σ_{i<m} c(i) ve c(n+1) = 0 ise,
P = Σ_{m≤n} c(m)·X^m için P = Π_{z∈Z}(1 − z·X) olan bir Z çoklu kümesi vardır ve
Σ_{z∈Z} z = −r, 2 ≤ k ≤ n+1 için Σ_{z∈Z} z^k = ε.
Yol: Newton benzeri evrişim özdeşliği (kuvvet serisi + çoklu küme tümevarımı) ve üçgen sistemin tekliği.
-/

set_option maxHeartbeats 4000000

open Polynomial

namespace Turan973.L2

noncomputable section

/-- Kuvvet toplamı p_l(Z) = Σ_{z∈Z} z^l. -/
def ps (Z : Multiset ℂ) (l : ℕ) : ℂ := (Z.map (fun z => z ^ l)).sum

/-- P_Z = Π_{z∈Z} (1 − z·X). -/
def PZ (Z : Multiset ℂ) : ℂ[X] := (Z.map (fun z => 1 - C z * X)).prod

/-- S_Z = Σ_l p_l·t^l (biçimsel kuvvet serisi). -/
def SZ (Z : Multiset ℂ) : PowerSeries ℂ := PowerSeries.mk (ps Z)

/-- Ailenin beklenen kuvvet toplamları: d, −r, ε, ε, … -/
def pyildiz (d r ε : ℂ) (k : ℕ) : ℂ := if k = 0 then d else if k = 1 then -r else ε

/-- Δ*_n: z 0 = 1, |z_j| ≥ 1 (j < n) dizilişlerinde max_{2≤k≤n+1} |p_k|'nin en küçüğü (|w|² = normSq w). -/
def DeltaStar (n : ℕ) : ℝ :=
  sInf {M : ℝ | 0 ≤ M ∧ ∃ z : ℕ → ℂ, z 0 = 1 ∧ (∀ j, j < n → 1 ≤ Complex.normSq (z j)) ∧
    ∀ k, 2 ≤ k → k ≤ n + 1 → Complex.normSq (∑ j ∈ Finset.range n, z j ^ k) ≤ M ^ 2}


theorem ps_bos (l : ℕ) : ps 0 l = 0 := by
  simp [ps]

theorem ps_cons (a : ℂ) (Z : Multiset ℂ) (l : ℕ) : ps (a ::ₘ Z) l = a ^ l + ps Z l := by
  simp [ps]

theorem PZ_bos : PZ 0 = 1 := by
  simp [PZ]

theorem PZ_cons (a : ℂ) (Z : Multiset ℂ) : PZ (a ::ₘ Z) = (1 - C a * X) * PZ Z := by
  simp [PZ]

theorem SZ_cons (a : ℂ) (Z : Multiset ℂ) :
    SZ (a ::ₘ Z) = PowerSeries.mk (fun l => a ^ l) + SZ Z := by
  ext l
  simp [SZ, ps_cons]

theorem geo (a : ℂ) :
    ((1 - C a * X : ℂ[X]) : PowerSeries ℂ) * PowerSeries.mk (fun l => a ^ l) = 1 := by
  have h : ((1 - C a * X : ℂ[X]) : PowerSeries ℂ) * PowerSeries.mk (fun l => a ^ l)
      = PowerSeries.mk (fun l => a ^ l)
        - ((C a : ℂ[X]) : PowerSeries ℂ) * (((X : ℂ[X]) : PowerSeries ℂ) * PowerSeries.mk (fun l => a ^ l)) := by
    push_cast
    ring
  rw [h]
  ext n
  rcases n with _ | n
  · first
    | simp [Polynomial.coe_C, Polynomial.coe_X, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul]
    | simp
  · first
    | (simp [Polynomial.coe_C, Polynomial.coe_X, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, pow_succ]; ring)
    | simp [Polynomial.coe_C, Polynomial.coe_X, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, pow_succ, mul_comm]
    | (simp [pow_succ] <;> ring)

theorem N1_seri (Z : Multiset ℂ) :
    ((PZ Z : ℂ[X]) : PowerSeries ℂ) * SZ Z
      = ((C ((Multiset.card Z : ℕ) : ℂ) * PZ Z - X * derivative (PZ Z) : ℂ[X]) : PowerSeries ℂ) := by
  induction Z using Multiset.induction_on with
  | empty =>
    have hS : SZ 0 = 0 := by
      ext l
      simp [SZ, ps_bos]
    rw [hS, PZ_bos]
    simp
  | cons a Z ih =>
    have hpol : PZ Z + (1 - C a * X) * (C ((Multiset.card Z : ℕ) : ℂ) * PZ Z - X * derivative (PZ Z))
        = C (((Multiset.card Z + 1 : ℕ)) : ℂ) * ((1 - C a * X) * PZ Z)
          - X * derivative ((1 - C a * X) * PZ Z) := by
      rw [derivative_mul, derivative_sub, derivative_one, derivative_mul, derivative_C, derivative_X]
      push_cast
      try simp only [map_add, map_one, map_natCast]
      ring
    rw [PZ_cons, SZ_cons, Multiset.card_cons]
    calc (((1 - C a * X) * PZ Z : ℂ[X]) : PowerSeries ℂ) * (PowerSeries.mk (fun l => a ^ l) + SZ Z)
        = ((PZ Z : ℂ[X]) : PowerSeries ℂ) * (((1 - C a * X : ℂ[X]) : PowerSeries ℂ) * PowerSeries.mk (fun l => a ^ l))
          + ((1 - C a * X : ℂ[X]) : PowerSeries ℂ) * (((PZ Z : ℂ[X]) : PowerSeries ℂ) * SZ Z) := by
          push_cast
          ring
      _ = ((PZ Z : ℂ[X]) : PowerSeries ℂ) * 1
          + ((1 - C a * X : ℂ[X]) : PowerSeries ℂ)
            * ((C ((Multiset.card Z : ℕ) : ℂ) * PZ Z - X * derivative (PZ Z) : ℂ[X]) : PowerSeries ℂ) := by
          rw [geo, ih]
      _ = ((PZ Z + (1 - C a * X) * (C ((Multiset.card Z : ℕ) : ℂ) * PZ Z - X * derivative (PZ Z)) : ℂ[X])
            : PowerSeries ℂ) := by
          push_cast
          ring
      _ = _ := by rw [hpol]

theorem N1 (Z : Multiset ℂ) (m : ℕ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, (PZ Z).coeff x.1 * ps Z x.2
      = ((Multiset.card Z : ℂ) - m) * (PZ Z).coeff m := by
  have h := congrArg (PowerSeries.coeff m) (N1_seri Z)
  rw [PowerSeries.coeff_mul] at h
  simp only [Polynomial.coeff_coe, SZ, PowerSeries.coeff_mk] at h
  first
  | rw [h]
  | refine h.trans ?_
  rcases m with _ | m
  · simp
  · first
    | (rw [coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative]; push_cast; ring)
    | (simp [coeff_derivative]; ring)

theorem N1_aralik (Z : Multiset ℂ) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (PZ Z).coeff i * ps Z (m - i)
      = ((Multiset.card Z : ℂ) - m) * (PZ Z).coeff m := by
  rw [← N1 Z m]
  first
  | rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i l => (PZ Z).coeff i * ps Z l) m]
  | (rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]; rfl)
  | simp [Finset.Nat.sum_antidiagonal_eq_sum_range_succ]

theorem tekillik (c x y : ℕ → ℂ) (h0 : c 0 = 1) (N : ℕ)
    (h : ∀ k, k ≤ N → ∑ i ∈ Finset.range (k + 1), c i * x (k - i)
                    = ∑ i ∈ Finset.range (k + 1), c i * y (k - i)) :
    ∀ k, k ≤ N → x k = y k := by
  have key : ∀ M, ∀ k, k ≤ M → k ≤ N → x k = y k := by
    intro M
    induction M with
    | zero =>
      intro k hk hkN
      have hk0 : k = 0 := by omega
      subst hk0
      simpa [h0] using h 0 hkN
    | succ M ihM =>
      intro k hk hkN
      have hk' := h k hkN
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hk'
      have hsum : ∑ i ∈ Finset.range k, c (i + 1) * x (k - (i + 1))
                = ∑ i ∈ Finset.range k, c (i + 1) * y (k - (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [ihM (k - (i + 1)) (by omega) (by omega)]
      simp only [hsum, h0, Nat.sub_zero, one_mul] at hk'
      exact add_left_cancel hk'
  intro k hk
  exact key k k le_rfl hk

theorem pyildiz_sistem (d r ε : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hrec : ∀ m : ℕ, ((m : ℂ) + 1) * c (m + 1) = r * c m - ε * ∑ i ∈ Finset.range m, c i) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), c i * pyildiz d r ε (k - i) = (d - (k : ℂ)) * c k := by
  have h1 : c 1 = r := by simpa [h0] using hrec 0
  have p1 : pyildiz d r ε 1 = -r := by simp [pyildiz]
  have p0 : pyildiz d r ε 0 = d := by simp [pyildiz]
  rcases k with _ | _ | j
  · simp [pyildiz, h0]
  · first
    | (simp [Finset.sum_range_succ, p0, p1, h0, h1]; ring)
    | simp [Finset.sum_range_succ, p0, p1, h0, h1]
  · show ∑ i ∈ Finset.range (j + 3), c i * pyildiz d r ε (j + 2 - i) = (d - ((j + 2 : ℕ) : ℂ)) * c (j + 2)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hs : ∑ i ∈ Finset.range (j + 1), c i * pyildiz d r ε (j + 2 - i)
        = ε * ∑ i ∈ Finset.range (j + 1), c i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have e1 : j + 2 - i ≠ 0 := by omega
      have e2 : j + 2 - i ≠ 1 := by omega
      simp only [pyildiz, e1, e2, if_false]
      ring
    have e3 : j + 2 - (j + 1) = 1 := by omega
    have e4 : j + 2 - (j + 2) = 0 := by omega
    rw [hs, e3, e4, p1, p0]
    have hr : (((j + 1 : ℕ) : ℂ) + 1) * c (j + 2) = r * c (j + 1) - ε * ∑ i ∈ Finset.range (j + 1), c i :=
      hrec (j + 1)
    push_cast at hr ⊢
    linear_combination hr

theorem esit_nota (n : ℕ) (r ε : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hrec : ∀ m : ℕ, ((m : ℂ) + 1) * c (m + 1) = r * c m - ε * ∑ i ∈ Finset.range m, c i)
    (Z : Multiset ℂ) (hc : ∀ i, i ≤ n + 1 → (PZ Z).coeff i = c i) :
    ps Z 1 = -r ∧ ∀ k, 2 ≤ k → k ≤ n + 1 → ps Z k = ε := by
  have hsis : ∀ k, k ≤ n + 1 → ∑ i ∈ Finset.range (k + 1), c i * ps Z (k - i)
      = ∑ i ∈ Finset.range (k + 1), c i * pyildiz (Multiset.card Z : ℂ) r ε (k - i) := by
    intro k hk
    rw [pyildiz_sistem (Multiset.card Z : ℂ) r ε c h0 hrec k, ← hc k hk, ← N1_aralik Z k]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hc i (by omega)]
  have heq := tekillik c (ps Z) (pyildiz (Multiset.card Z : ℂ) r ε) h0 (n + 1) hsis
  constructor
  · rw [heq 1 (by omega)]
    simp [pyildiz]
  · intro k hk2 hk
    rw [heq k hk]
    have e1 : k ≠ 0 := by omega
    have e2 : k ≠ 1 := by omega
    simp [pyildiz, e1, e2]

theorem PZ_coeff_zero (Z : Multiset ℂ) : (PZ Z).coeff 0 = 1 := by
  first
  | (rw [Polynomial.coeff_zero_eq_eval_zero, PZ, Polynomial.eval_multiset_prod]; simp)
  | simp [PZ, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod]

theorem ayrisim (P : ℂ[X]) (h0 : P.coeff 0 = 1) :
    ∃ Z : Multiset ℂ, PZ Z = P ∧ Multiset.card Z = P.natDegree := by
  classical
  have hP : P ≠ 0 := by
    intro h
    rw [h, Polynomial.coeff_zero] at h0
    exact zero_ne_one h0
  have hsplit : Multiset.card P.roots = P.natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits P)
  have hnz : ∀ u ∈ P.roots, u ≠ 0 := by
    intro u hu hu0
    have hr := (Polynomial.mem_roots hP).mp hu
    rw [hu0] at hr
    have h00 : P.eval 0 = 0 := hr
    rw [← Polynomial.coeff_zero_eq_eval_zero, h0] at h00
    exact one_ne_zero h00
  have hlin : ∀ u ∈ P.roots, X - C u = C (-u) * (1 - C u⁻¹ * X) := by
    intro u hu
    have hu0 := hnz u hu
    have hc : C (-u) * C u⁻¹ = (-1 : ℂ[X]) := by
      rw [← C_mul, neg_mul, mul_inv_cancel₀ hu0, C_neg, C_1]
    calc X - C u = C (-u) - (-1 : ℂ[X]) * X := by rw [C_neg]; ring
      _ = C (-u) - (C (-u) * C u⁻¹) * X := by rw [hc]
      _ = C (-u) * (1 - C u⁻¹ * X) := by ring
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  rw [Multiset.map_congr rfl hlin, Multiset.prod_map_mul] at hfac
  have hPZ : PZ (P.roots.map (fun u => u⁻¹)) = (P.roots.map (fun u => 1 - C u⁻¹ * X)).prod := by
    simp [PZ, Multiset.map_map, Function.comp_def]
  have hCprod : (P.roots.map (fun u => C (-u))).prod = C ((P.roots.map (fun u => -u)).prod) := by
    first
    | (rw [map_multiset_prod C, Multiset.map_map]; rfl)
    | simp [map_multiset_prod, Multiset.map_map, Function.comp_def]
  have hPk : P = C (P.leadingCoeff * (P.roots.map (fun u => -u)).prod) * PZ (P.roots.map (fun u => u⁻¹)) := by
    rw [hPZ, C_mul, ← hCprod, mul_assoc]
    exact hfac.symm
  have hk1 : P.leadingCoeff * (P.roots.map (fun u => -u)).prod = 1 := by
    have h2 := congrArg (fun p => Polynomial.coeff p 0) hPk
    simp only [Polynomial.coeff_C_mul, PZ_coeff_zero, mul_one, h0] at h2
    exact h2.symm
  refine ⟨P.roots.map (fun u => u⁻¹), ?_, by rw [Multiset.card_map, hsplit]⟩
  calc PZ (P.roots.map (fun u => u⁻¹)) = C 1 * PZ (P.roots.map (fun u => u⁻¹)) := by rw [C_1, one_mul]
    _ = C (P.leadingCoeff * (P.roots.map (fun u => -u)).prod) * PZ (P.roots.map (fun u => u⁻¹)) := by rw [hk1]
    _ = P := hPk.symm

theorem aile_katsayi (n : ℕ) (c : ℕ → ℂ) (i : ℕ) :
    (∑ m ∈ Finset.range (n + 1), C (c m) * X ^ m).coeff i = if i < n + 1 then c i else 0 := by
  first
  | (rw [Polynomial.finset_sum_coeff]; simp [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.sum_ite_eq'])
  | (simp only [← Polynomial.lcoeff_apply, map_sum]
     simp [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.sum_ite_eq'])
  | simp [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem aile_esit_nota (n : ℕ) (r ε : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hrec : ∀ m : ℕ, ((m : ℂ) + 1) * c (m + 1) = r * c m - ε * ∑ i ∈ Finset.range m, c i)
    (hkapa : c (n + 1) = 0) :
    ∃ Z : Multiset ℂ, PZ Z = ∑ m ∈ Finset.range (n + 1), C (c m) * X ^ m ∧
      ps Z 1 = -r ∧ ∀ k, 2 ≤ k → k ≤ n + 1 → ps Z k = ε := by
  have hP0 : (∑ m ∈ Finset.range (n + 1), C (c m) * X ^ m).coeff 0 = 1 := by
    rw [aile_katsayi]
    simp [h0]
  obtain ⟨Z, hZ, -⟩ := ayrisim _ hP0
  refine ⟨Z, hZ, ?_⟩
  apply esit_nota n r ε c h0 hrec Z
  intro i hi
  rw [hZ, aile_katsayi]
  by_cases hin : i < n + 1
  · simp [hin]
  · have hi1 : i = n + 1 := by omega
    subst hi1
    simp [hkapa]

theorem ps_olcek (w : ℂ) (Z : Multiset ℂ) (k : ℕ) :
    ps (Z.map (fun z => w * z)) k = w ^ k * ps Z k := by
  simp [ps, Multiset.map_map, Function.comp_def, mul_pow, Multiset.sum_map_mul_left]

theorem DeltaStar_le (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∃ z : ℕ → ℂ, z 0 = 1 ∧ (∀ j, j < n → 1 ≤ Complex.normSq (z j)) ∧
      ∀ k, 2 ≤ k → k ≤ n + 1 → Complex.normSq (∑ j ∈ Finset.range n, z j ^ k) ≤ B ^ 2) :
    DeltaStar n ≤ B := by
  apply csInf_le
  · exact ⟨0, fun M hM => hM.1⟩
  · exact ⟨hB, h⟩

end

end Turan973.L2

#print axioms Turan973.L2.ps_bos
#print axioms Turan973.L2.ps_cons
#print axioms Turan973.L2.PZ_bos
#print axioms Turan973.L2.PZ_cons
#print axioms Turan973.L2.SZ_cons
#print axioms Turan973.L2.geo
#print axioms Turan973.L2.N1_seri
#print axioms Turan973.L2.N1
#print axioms Turan973.L2.N1_aralik
#print axioms Turan973.L2.tekillik
#print axioms Turan973.L2.pyildiz_sistem
#print axioms Turan973.L2.esit_nota
#print axioms Turan973.L2.PZ_coeff_zero
#print axioms Turan973.L2.ayrisim
#print axioms Turan973.L2.aile_katsayi
#print axioms Turan973.L2.aile_esit_nota
#print axioms Turan973.L2.ps_olcek
#print axioms Turan973.L2.DeltaStar_le

theorem Turan973.L2.yanlis_nota (n : ℕ) (r ε : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hrec : ∀ m : ℕ, ((m : ℂ) + 1) * c (m + 1) = r * c m - ε * ∑ i ∈ Finset.range m, c i)
    (Z : Multiset ℂ) (hc : ∀ i, i ≤ n + 1 → (Turan973.L2.PZ Z).coeff i = c i) (hn : 1 ≤ n) :
    Turan973.L2.ps Z 2 = ε + 1 := by
  rw [(Turan973.L2.esit_nota n r ε c h0 hrec Z hc).2 2 le_rfl (by omega)]
  ring
#print axioms Turan973.L2.yanlis_nota
