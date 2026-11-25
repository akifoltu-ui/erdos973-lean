import Mathlib

/-!
# TURAN973 L1 — Erdős #973 dış hâl, n = 21 için kesin üst sınır

Üreten: turan973_lean_v1.py (md5 934fd2fbc3a069c886fce4b74d5c6de0), 2026-11-06 01:23. Yalnız Mathlib'e dayanır.

İddia (`ust_sinir`): z 0 = 1 ve |z j| ≥ 1 (j < 21) olan 21 karmaşık sayı vardır; her 2 ≤ k ≤ 22 için
  normSq (Σ_{j<21} z_j^k) · BDEN² ≤ BNUM²,  yani  |p_k| ≤ BNUM / BDEN = 0.16583127057988.
Dolayısıyla Δ*_21 ≤ 0.16583127057988.

Kanıt yolu: z_j = w_j / S, w_j Gauss tam sayısı, S = 2^115. Üç tam sayı denetimi (`bir_ok`, `nokta_ok`,
`toplam_ok`) çekirdekte `decide` ile hesaplanır; köprü lemmaları hesabı ℂ'deki ifadeye bağlar.
Derleyiciye güvenen (native) karar verici kullanılmaz; ek aksiyom yoktur.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Turan973.N21

/-- Gauss tam sayısı a + b·i. -/
structure GZ where
  re : Int
  im : Int
deriving DecidableEq

def GZ.mul (x y : GZ) : GZ := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩

def GZ.add (x y : GZ) : GZ := ⟨x.re + y.re, x.im + y.im⟩

def GZ.pw (x : GZ) : Nat → GZ
  | 0 => ⟨1, 0⟩
  | k + 1 => GZ.mul (GZ.pw x k) x

def GZ.nsq (x : GZ) : Int := x.re * x.re + x.im * x.im

def ipow (s : Int) : Nat → Int
  | 0 => 1
  | k + 1 => ipow s k * s

def nth : List GZ → Nat → GZ
  | [], _ => ⟨0, 0⟩
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nth xs n

/-- Ölçek S = 2^115. -/
def S : Int := 41538374868278621028243970633760768
/-- Sınır B = BNUM / BDEN = 0.16583127057988. -/
def BNUM : Int := 16583127057988
def BDEN : Int := 100000000000000

/-- w_j = S · z_j (j = 0 … 20); w_0 = S, yani z_0 = 1. -/
def pts : List GZ := [
  ⟨41538374868278621028243970633760768, 0⟩,
  ⟨-45063444595843250854517990864088299, -72261420770392812134623075382496219⟩,
  ⟨-70693488408215243118140266166559303, -47485341604288044343570290358384254⟩,
  ⟨-28430172224246788018668222789123497, -78861023671692496602716101734120689⟩,
  ⟨-77852733550168072680791211167998164, -31085167299117314198149194234004659⟩,
  ⟨-80488287838250206815722488990293708, -13546630846389494340023199150355304⟩,
  ⟨-10812424892188076247183852908859479, -80900971282007233798605540526724239⟩,
  ⟨6493784033056630197823219900604002, -78280684616516875914841106657855318⟩,
  ⟨-78455729308114261385722270360012030, 3838405115469708010257308277014727⟩,
  ⟨22202776657977694856483054440455783, -71255483231792882022928713684936220⟩,
  ⟨-71966680395132339562882799766559415, 19776351908914604601776792623395791⟩,
  ⟨-61575652069087192832721665912448984, 33061320805592102968271009582108376⟩,
  ⟨35128139594518983887264188790640003, -60420407725962482042525946165359186⟩,
  ⟨-48142825779433375675856234163564928, 42651123596908366492261327572456350⟩,
  ⟨44257420204439072066328246640070962, -46670448626034619412983048181337442⟩,
  ⟨48796303115483174228587401169466551, -31140855622732871644362497422052686⟩,
  ⟨-32775893364986150456033971774041675, 47713445702244805300198795248019195⟩,
  ⟨-59498745070448207698819899257243894, -61549506389331144617568459188713229⟩,
  ⟨-1407056251981110306177789616828554, 41514536964795859530348838002625374⟩,
  ⟨-16753424061242747477795887973794250, 47599081196469242286071518732133966⟩,
  ⟨48139264769735806887332966680030801, -15131455182935057018485231315376440⟩
]

def pt (j : Nat) : GZ := nth pts j

def psum (k : Nat) : Nat → GZ
  | 0 => ⟨0, 0⟩
  | m + 1 => GZ.add (psum k m) (GZ.pw (pt m) k)

theorem bir_ok : pt 0 = ⟨S, 0⟩ := by first | decide +kernel | decide

theorem nokta_ok : ∀ j, j < 21 → S * S ≤ (pt j).nsq := by first | decide +kernel | decide

theorem toplam_ok : ∀ m, m < 21 →
    (psum (m + 2) 21).nsq * (BDEN * BDEN) ≤ (BNUM * BNUM) * ipow S (2 * (m + 2)) := by first | decide +kernel | decide

theorem S_pos : (0 : Int) < S := by first | decide +kernel | decide

noncomputable section

def GZ.toC (x : GZ) : ℂ := ⟨(x.re : ℝ), (x.im : ℝ)⟩

theorem toC_re (x : GZ) : x.toC.re = (x.re : ℝ) := rfl
theorem toC_im (x : GZ) : x.toC.im = (x.im : ℝ) := rfl

theorem toC_one : (GZ.mk 1 0).toC = 1 := by
  apply Complex.ext
  · first
    | (simp [toC_re])
    | (rw [toC_re, Complex.one_re]; norm_num)
  · first
    | (simp [toC_im])
    | (rw [toC_im, Complex.one_im]; norm_num)

theorem toC_zero : (GZ.mk 0 0).toC = 0 := by
  apply Complex.ext
  · first
    | (simp [toC_re])
    | (rw [toC_re, Complex.zero_re]; norm_num)
  · first
    | (simp [toC_im])
    | (rw [toC_im, Complex.zero_im]; norm_num)

theorem toC_add (x y : GZ) : (GZ.add x y).toC = x.toC + y.toC := by
  apply Complex.ext
  · first
    | (simp [toC_re, GZ.add])
    | (simp only [toC_re, Complex.add_re, GZ.add]; push_cast <;> ring)
  · first
    | (simp [toC_im, GZ.add])
    | (simp only [toC_im, Complex.add_im, GZ.add]; push_cast <;> ring)

theorem toC_mul (x y : GZ) : (GZ.mul x y).toC = x.toC * y.toC := by
  apply Complex.ext
  · first
    | (simp only [toC_re, toC_im, Complex.mul_re, GZ.mul]; push_cast <;> ring)
    | (simp [toC_re, toC_im, Complex.mul_re, GZ.mul])
    | (simp [toC_re, toC_im, GZ.mul] <;> ring)
  · first
    | (simp only [toC_re, toC_im, Complex.mul_im, GZ.mul]; push_cast <;> ring)
    | (simp [toC_re, toC_im, Complex.mul_im, GZ.mul])
    | (simp [toC_re, toC_im, GZ.mul] <;> ring)

theorem toC_pw (x : GZ) : ∀ k : Nat, (GZ.pw x k).toC = x.toC ^ k
  | 0 => by
    first
    | (show (GZ.mk 1 0).toC = x.toC ^ 0; rw [pow_zero]; exact toC_one)
    | (simp [GZ.pw, toC_one])
  | k + 1 => by
    first
    | (show (GZ.mul (GZ.pw x k) x).toC = x.toC ^ (k + 1); rw [toC_mul, toC_pw x k]; ring)
    | (simp only [GZ.pw]; rw [toC_mul, toC_pw x k]; ring)

theorem toC_psum (k : Nat) : ∀ m : Nat, (psum k m).toC = ∑ j ∈ Finset.range m, (pt j).toC ^ k
  | 0 => by
    first
    | (show (GZ.mk 0 0).toC = _; rw [Finset.sum_range_zero]; exact toC_zero)
    | (simp [psum, toC_zero])
  | m + 1 => by
    first
    | (show (GZ.add (psum k m) (GZ.pw (pt m) k)).toC = _
       rw [toC_add, toC_psum k m, toC_pw, Finset.sum_range_succ])
    | (simp only [psum]; rw [toC_add, toC_psum k m, toC_pw, Finset.sum_range_succ])

theorem normSq_toC (x : GZ) : Complex.normSq x.toC = (x.nsq : ℝ) := by
  first
  | (rw [Complex.normSq_apply, toC_re, toC_im]; simp only [GZ.nsq]; push_cast <;> ring)
  | (simp [Complex.normSq_apply, toC_re, toC_im, GZ.nsq])
  | (rw [Complex.normSq_apply]; simp [toC_re, toC_im, GZ.nsq] <;> ring)

theorem ipow_cast (s : Int) : ∀ k : Nat, ((ipow s k : Int) : ℝ) = (s : ℝ) ^ k
  | 0 => by
    first
    | (show ((1 : Int) : ℝ) = (s : ℝ) ^ 0; simp)
    | (simp [ipow])
  | k + 1 => by
    first
    | (show ((ipow s k * s : Int) : ℝ) = (s : ℝ) ^ (k + 1); push_cast; rw [ipow_cast s k]; ring)
    | (simp only [ipow]; push_cast; rw [ipow_cast s k]; ring)

/-- Ana teorem: Δ*_21 ≤ 0.16583127057988 (|z|² = normSq z biçiminde, bölmesiz). -/
theorem ust_sinir :
    ∃ z : ℕ → ℂ, z 0 = 1 ∧ (∀ j, j < 21 → 1 ≤ Complex.normSq (z j)) ∧
      (∀ k, 2 ≤ k → k ≤ 22 →
        Complex.normSq (∑ j ∈ Finset.range 21, z j ^ k) * ((BDEN : ℝ) ^ 2) ≤ (BNUM : ℝ) ^ 2) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast S_pos
  obtain ⟨r, hSr⟩ : ∃ r : ℝ, (S : ℝ) * r = 1 :=
    ⟨(S : ℝ)⁻¹, by first | exact mul_inv_cancel₀ (ne_of_gt hSpos) | field_simp⟩
  refine ⟨fun j => (pt j).toC * (r : ℂ), ?_, ?_, ?_⟩
  · show (pt 0).toC * (r : ℂ) = 1
    rw [bir_ok]
    apply Complex.ext
    · first
      | (simp [Complex.mul_re, toC_re, toC_im, hSr])
      | (simp only [Complex.mul_re, toC_re, toC_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re]
         push_cast; linarith [hSr])
    · first
      | (simp [Complex.mul_im, toC_re, toC_im])
      | (simp only [Complex.mul_im, toC_re, toC_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_im]
         push_cast; ring)
  · intro j hj
    show 1 ≤ Complex.normSq ((pt j).toC * (r : ℂ))
    rw [Complex.normSq_mul, normSq_toC, Complex.normSq_ofReal]
    have h1 : ((S : ℝ) * S) ≤ ((pt j).nsq : ℝ) := by exact_mod_cast nokta_ok j hj
    calc (1 : ℝ) = ((S : ℝ) * r) * ((S : ℝ) * r) := by rw [hSr, one_mul]
      _ = ((S : ℝ) * S) * (r * r) := by ring
      _ ≤ ((pt j).nsq : ℝ) * (r * r) := mul_le_mul_of_nonneg_right h1 (mul_self_nonneg r)
  · intro k hk2 hkK
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hm : m < 21 := by omega
    have hsum : (∑ j ∈ Finset.range 21, ((pt j).toC * (r : ℂ)) ^ (m + 2))
        = (psum (m + 2) 21).toC * ((r ^ (m + 2) : ℝ) : ℂ) := by
      rw [toC_psum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_pow, Complex.ofReal_pow]
    show Complex.normSq (∑ j ∈ Finset.range 21, ((pt j).toC * (r : ℂ)) ^ (m + 2)) * ((BDEN : ℝ) ^ 2)
        ≤ (BNUM : ℝ) ^ 2
    rw [hsum, Complex.normSq_mul, normSq_toC, Complex.normSq_ofReal]
    have h3 : (((psum (m + 2) 21).nsq * (BDEN * BDEN) : Int) : ℝ)
        ≤ (((BNUM * BNUM) * ipow S (2 * (m + 2)) : Int) : ℝ) := by exact_mod_cast toplam_ok m hm
    push_cast at h3
    rw [ipow_cast] at h3
    calc ((psum (m + 2) 21).nsq : ℝ) * (r ^ (m + 2) * r ^ (m + 2)) * (BDEN : ℝ) ^ 2
        = (((psum (m + 2) 21).nsq : ℝ) * ((BDEN : ℝ) * BDEN)) * (r ^ (m + 2) * r ^ (m + 2)) := by ring
      _ ≤ ((BNUM : ℝ) * BNUM * (S : ℝ) ^ (2 * (m + 2))) * (r ^ (m + 2) * r ^ (m + 2)) :=
          mul_le_mul_of_nonneg_right h3 (mul_self_nonneg _)
      _ = (BNUM : ℝ) ^ 2 * ((S : ℝ) * r) ^ (2 * (m + 2)) := by ring
      _ = (BNUM : ℝ) ^ 2 := by rw [hSr, one_pow, mul_one]

end

end Turan973.N21

#print axioms Turan973.N21.ust_sinir

/-! ## L2'den aynen (Turan973_L2_v2.lean, TURAN973_v05): Δ*ₙ tanımı ve DeltaStar_le -/

namespace Turan973.L2

noncomputable section

/-- Δ*_n: z 0 = 1, |z_j| ≥ 1 (j < n) dizilişlerinde max_{2≤k≤n+1} |p_k|'nin en küçüğü (|w|² = normSq w). -/
def DeltaStar (n : ℕ) : ℝ :=
  sInf {M : ℝ | 0 ≤ M ∧ ∃ z : ℕ → ℂ, z 0 = 1 ∧ (∀ j, j < n → 1 ≤ Complex.normSq (z j)) ∧
    ∀ k, 2 ≤ k → k ≤ n + 1 → Complex.normSq (∑ j ∈ Finset.range n, z j ^ k) ≤ M ^ 2}

theorem DeltaStar_le (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∃ z : ℕ → ℂ, z 0 = 1 ∧ (∀ j, j < n → 1 ≤ Complex.normSq (z j)) ∧
      ∀ k, 2 ≤ k → k ≤ n + 1 → Complex.normSq (∑ j ∈ Finset.range n, z j ^ k) ≤ B ^ 2) :
    DeltaStar n ≤ B := by
  apply csInf_le
  · exact ⟨0, fun M hM => hM.1⟩
  · exact ⟨hB, h⟩

end

end Turan973.L2

namespace Turan973.Birlesim

/-- L1 + L2: Δ*_21 ≤ BNUM / BDEN (= 0.16583127057988). -/
theorem N21_DeltaStar : Turan973.L2.DeltaStar 21 ≤ (Turan973.N21.BNUM : ℝ) / (Turan973.N21.BDEN : ℝ) := by
  have hD : (0 : ℝ) < (Turan973.N21.BDEN : ℝ) := by
    first
    | exact_mod_cast (show (0 : Int) < Turan973.N21.BDEN by decide)
    | (unfold Turan973.N21.BDEN; norm_num)
    | (norm_num [Turan973.N21.BDEN])
  have hN : (0 : ℝ) ≤ (Turan973.N21.BNUM : ℝ) := by
    first
    | exact_mod_cast (show (0 : Int) ≤ Turan973.N21.BNUM by decide)
    | (norm_num [Turan973.N21.BNUM])
  obtain ⟨z, h0, h1, h2⟩ := Turan973.N21.ust_sinir
  refine Turan973.L2.DeltaStar_le 21 _ (div_nonneg hN hD.le) ⟨z, h0, h1, fun k hk1 hk2 => ?_⟩
  have h := h2 k hk1 (by omega)
  have hD2 : (0 : ℝ) < (Turan973.N21.BDEN : ℝ) ^ 2 := pow_pos hD 2
  first
  | (rw [div_pow, le_div_iff₀ hD2]; exact h)
  | (rw [div_pow]; exact (le_div_iff₀ hD2).mpr h)
  | (rw [div_pow, le_div_iff hD2]; exact h)

end Turan973.Birlesim

#print axioms Turan973.L2.DeltaStar_le
#print axioms Turan973.Birlesim.N21_DeltaStar

/-- NEGATIF (sahte). -/
theorem Turan973.Birlesim.sahte_negatif : Turan973.L2.DeltaStar 21 ≤ (Turan973.N21.BNUM : ℝ) / (Turan973.N21.BDEN : ℝ) := by
  sorry
#print axioms Turan973.Birlesim.sahte_negatif
