import Mathlib

/-!
# TURAN973 L1 — Erdős #973 dış hâl, n = 31 için kesin üst sınır

Üreten: turan973_lean_v1.py (md5 934fd2fbc3a069c886fce4b74d5c6de0), 2026-11-06 01:23. Yalnız Mathlib'e dayanır.

İddia (`ust_sinir`): z 0 = 1 ve |z j| ≥ 1 (j < 31) olan 31 karmaşık sayı vardır; her 2 ≤ k ≤ 32 için
  normSq (Σ_{j<31} z_j^k) · BDEN² ≤ BNUM²,  yani  |p_k| ≤ BNUM / BDEN = 0.14523372410223.
Dolayısıyla Δ*_31 ≤ 0.14523372410223.

Kanıt yolu: z_j = w_j / S, w_j Gauss tam sayısı, S = 2^131. Üç tam sayı denetimi (`bir_ok`, `nokta_ok`,
`toplam_ok`) çekirdekte `decide` ile hesaplanır; köprü lemmaları hesabı ℂ'deki ifadeye bağlar.
Derleyiciye güvenen (native) karar verici kullanılmaz; ek aksiyom yoktur.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Turan973.N31

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

/-- Ölçek S = 2^131. -/
def S : Int := 2722258935367507707706996859454145691648
/-- Sınır B = BNUM / BDEN = 0.14523372410223. -/
def BNUM : Int := 14523372410223
def BDEN : Int := 100000000000000

/-- w_j = S · z_j (j = 0 … 30); w_0 = S, yani z_0 = 1. -/
def pts : List GZ := [
  ⟨2722258935367507707706996859454145691648, 0⟩,
  ⟨-4306711584974829432665313389927361855845, -4411146782512302611971241404093112047725⟩,
  ⟨-5401479055209744374532514592971196907280, -2971532370538051924465208933147981145682⟩,
  ⟨-3584761270896354235516324551272095571452, -4958575964657578596730272061494827758930⟩,
  ⟨-5736109557279883101438873920021981987296, -2129562423006347195223482040200779758822⟩,
  ⟨-2779225165021853335125224199255639761858, -5364618258393628416466224823493382222364⟩,
  ⟨-5912160246545869544302118567627060902510, -1244822395100488980486322703196155034966⟩,
  ⟨-1918896194600996989237526443238010474980, -5615783309731926852380235308972171102757⟩,
  ⟨-5924324347574428969777656356449256821126, -348662891995518385325464691176424083009⟩,
  ⟨-5773387413291427717394735371659373868612, 527016751528004341597706149342160980735⟩,
  ⟨-1034723864921339112443872048612894274501, -5704304988664724213389665824690312507262⟩,
  ⟨-5466224254190408287208998788141791782637, 1350892885388712656601519092857900027268⟩,
  ⟨-158729903297351708822839873125798859930, -5628438860171845220675140452995972162082⟩,
  ⟨-5015587326993079280836829383376013425021, 2093303844376165731037943833517845092913⟩,
  ⟨677095088029772035299654107321016892167, -5392548512655177951773021890620259713232⟩,
  ⟨1441862536538765926916584092891243040292, -5006979342658879580199838020332834844162⟩,
  ⟨-4439698974991385463740958225834608284383, 2727248196176356670057371437484429568983⟩,
  ⟨-3761670312307825509409138415178179221483, 3229238738213634665890091047940639833481⟩,
  ⟨2106764115919413674361492364017190456434, -4487726743770383812840430343774439471936⟩,
  ⟨-3008781862178377734370555254253848170986, 3579940910346946084584873584224009100343⟩,
  ⟨2645879153796507828738606612115538188462, -3855913474036260472250924206102731736907⟩,
  ⟨727355279963015681167761169492279165335, 2623289539471035893732690458213583149662⟩,
  ⟨-4919459462236115879538716047409117923103, -3741046314623708440804582903489178591716⟩,
  ⟨-2211677909172543493784604065593303656172, 3764483809602342420073098715512658412835⟩,
  ⟨3036689598856135352308749349856208100845, -3137096397447640173926641050817952938508⟩,
  ⟨-1403554684080265945091425600279585277772, 3772214027426596411389576132458715875463⟩,
  ⟨3260059714860811623823264153840496117191, -2360418411099879854589034543666062869112⟩,
  ⟨3134212581699636810424951194351884709883, -761227347379757011208317219992823008338⟩,
  ⟨103871945688726600986893469043215471871, 3223657270955143276139009358715843245800⟩,
  ⟨-619480444175457420493820100060708510441, 3595267744975702476644917222407937275028⟩,
  ⟨3299041754775286965764399422679684468957, -1557571725163143226718381718681910104659⟩
]

def pt (j : Nat) : GZ := nth pts j

def psum (k : Nat) : Nat → GZ
  | 0 => ⟨0, 0⟩
  | m + 1 => GZ.add (psum k m) (GZ.pw (pt m) k)

theorem bir_ok : pt 0 = ⟨S, 0⟩ := by first | decide +kernel | decide

theorem nokta_ok : ∀ j, j < 31 → S * S ≤ (pt j).nsq := by first | decide +kernel | decide

theorem toplam_ok : ∀ m, m < 31 →
    (psum (m + 2) 31).nsq * (BDEN * BDEN) ≤ (BNUM * BNUM) * ipow S (2 * (m + 2)) := by first | decide +kernel | decide

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

/-- Ana teorem: Δ*_31 ≤ 0.14523372410223 (|z|² = normSq z biçiminde, bölmesiz). -/
theorem ust_sinir :
    ∃ z : ℕ → ℂ, z 0 = 1 ∧ (∀ j, j < 31 → 1 ≤ Complex.normSq (z j)) ∧
      (∀ k, 2 ≤ k → k ≤ 32 →
        Complex.normSq (∑ j ∈ Finset.range 31, z j ^ k) * ((BDEN : ℝ) ^ 2) ≤ (BNUM : ℝ) ^ 2) := by
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
    have hm : m < 31 := by omega
    have hsum : (∑ j ∈ Finset.range 31, ((pt j).toC * (r : ℂ)) ^ (m + 2))
        = (psum (m + 2) 31).toC * ((r ^ (m + 2) : ℝ) : ℂ) := by
      rw [toC_psum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_pow, Complex.ofReal_pow]
    show Complex.normSq (∑ j ∈ Finset.range 31, ((pt j).toC * (r : ℂ)) ^ (m + 2)) * ((BDEN : ℝ) ^ 2)
        ≤ (BNUM : ℝ) ^ 2
    rw [hsum, Complex.normSq_mul, normSq_toC, Complex.normSq_ofReal]
    have h3 : (((psum (m + 2) 31).nsq * (BDEN * BDEN) : Int) : ℝ)
        ≤ (((BNUM * BNUM) * ipow S (2 * (m + 2)) : Int) : ℝ) := by exact_mod_cast toplam_ok m hm
    push_cast at h3
    rw [ipow_cast] at h3
    calc ((psum (m + 2) 31).nsq : ℝ) * (r ^ (m + 2) * r ^ (m + 2)) * (BDEN : ℝ) ^ 2
        = (((psum (m + 2) 31).nsq : ℝ) * ((BDEN : ℝ) * BDEN)) * (r ^ (m + 2) * r ^ (m + 2)) := by ring
      _ ≤ ((BNUM : ℝ) * BNUM * (S : ℝ) ^ (2 * (m + 2))) * (r ^ (m + 2) * r ^ (m + 2)) :=
          mul_le_mul_of_nonneg_right h3 (mul_self_nonneg _)
      _ = (BNUM : ℝ) ^ 2 * ((S : ℝ) * r) ^ (2 * (m + 2)) := by ring
      _ = (BNUM : ℝ) ^ 2 := by rw [hSr, one_pow, mul_one]

end

end Turan973.N31

#print axioms Turan973.N31.ust_sinir
