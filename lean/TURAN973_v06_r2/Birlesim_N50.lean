import Mathlib

/-!
# TURAN973 L1 — Erdős #973 dış hâl, n = 50 için kesin üst sınır

Üreten: turan973_lean_v1.py (md5 934fd2fbc3a069c886fce4b74d5c6de0), 2026-11-06 01:23. Yalnız Mathlib'e dayanır.

İddia (`ust_sinir`): z 0 = 1 ve |z j| ≥ 1 (j < 50) olan 50 karmaşık sayı vardır; her 2 ≤ k ≤ 51 için
  normSq (Σ_{j<50} z_j^k) · BDEN² ≤ BNUM²,  yani  |p_k| ≤ BNUM / BDEN = 0.12709904148206.
Dolayısıyla Δ*_50 ≤ 0.12709904148206.

Kanıt yolu: z_j = w_j / S, w_j Gauss tam sayısı, S = 2^163. Üç tam sayı denetimi (`bir_ok`, `nokta_ok`,
`toplam_ok`) çekirdekte `decide` ile hesaplanır; köprü lemmaları hesabı ℂ'deki ifadeye bağlar.
Derleyiciye güvenen (native) karar verici kullanılmaz; ek aksiyom yoktur.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Turan973.N50

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

/-- Ölçek S = 2^163. -/
def S : Int := 11692013098647223345629478661730264157247460343808
/-- Sınır B = BNUM / BDEN = 0.12709904148206. -/
def BNUM : Int := 12709904148206
def BDEN : Int := 100000000000000

/-- w_j = S · z_j (j = 0 … 49); w_0 = S, yani z_0 = 1. -/
def pts : List GZ := [
  ⟨11692013098647223345629478661730264157247460343808, 0⟩,
  ⟨-25001000769185659021316531453464873288629509434894, -15304094648831283893685173633447787960554674526574⟩,
  ⟨-23413070900488155806962554098205435133793618224706, -17540670103164748641549023782806737578183429483176⟩,
  ⟨-27359195929158230933966747163746076846516366114766, -10359603987087275794163164767658788714087221841460⟩,
  ⟨-28096561057513122625137768621135142904179681188405, -7721361650508893893157416290803882149054154790934⟩,
  ⟨-21581369514183405489214500704415547842172804667422, -19577554977289361967961780956097354855360364253197⟩,
  ⟨-19532158559829254399542639797803181897448498627466, -21386424516406388208064169942202089885159347708916⟩,
  ⟨-28524836691074127509995271534750628761994540459306, -5021758989618144680216366334452172797665145512474⟩,
  ⟨-28638824615883791614239567954261932620231720985577, -2299112748213287021618074392515687630885763025658⟩,
  ⟨-17294995531327469572267780402693345399525542436298, -22942347839306052943272301817083796784743069623731⟩,
  ⟨-28438041120879298147285347909574369214452794330464, 407852762647790075989347182323789332794598973493⟩,
  ⟨-14902309567368332096585733440440159995255397573152, -24224155222156738759942979145625845338846409203084⟩,
  ⟨-12388938825822083560275838515430303715970177861643, -25214751663872244487506083025291425496192349267274⟩,
  ⟨-27926733659626846782046437667350494343075811079853, 3060564295187228021123596678104668091252505374922⟩,
  ⟨-27113831575218224536143324870329321795438548400490, 5621153520483685469988049377459769133355628983515⟩,
  ⟨-9791636537875436435747142119406941396534189341475, -25901372231993610246896419759579175954529459122247⟩,
  ⟨-7148553884538624936392618727020440525235858793360, -26275775575390259469668119350347129504913270662373⟩,
  ⟨-26012832203425564784656802789332456611908409741248, 8052997298202294904757794538292771444393722710427⟩,
  ⟨-4498708570469517700358923749308938042657771866717, -26334372930325234181882112649494815749321551158176⟩,
  ⟨-24641624855519987098782112806742992533997200443519, 10321235435512646410231436659075056725263588834132⟩,
  ⟨-1881448750280122696007465956335129560994711856084, -26078290924746737216514699601755084865359705387656⟩,
  ⟨-23022256426291515040107034395818722400733580632627, 12393256876129765290534715660594279982221113788537⟩,
  ⟨-21180643708084085183150264208326424338561004828270, 14239145019109102555617384825928235919387839045802⟩,
  ⟨664077117929881372568976459047849961187319073474, -25513367483448033714340252076268783799690358262053⟩,
  ⟨3099432698526083534891621839124563630693327453035, -24650081128259180467340596100279848280213764243494⟩,
  ⟨-19146238981936835044251110797218645286389019022954, 15832072370003063438301275397323522522815729878289⟩,
  ⟨-16951657220012439282472456947270285529647808755797, 17148633713539503896781706608636987625145036359655⟩,
  ⟨5387374889756311750338305205808487966758165971212, -23503414912373195495964498765834984096253685161390⟩,
  ⟨-26322571253288176224501071757370904907011977643141, -12899131563666415457644359317059568092726484021098⟩,
  ⟨6268481985919034872562187771474028148547709545170, 9869615184552374327842180489235898928049721301032⟩,
  ⟨-14632275485830718482890150304649442546936479621970, 18169104991790052532425477903870119073660617942533⟩,
  ⟨7492287126405826818475091415568637059939763233784, -22092657054130594355637784063511253716618404871520⟩,
  ⟨9380543398234580014011936609815379935492004739311, -20441140898541872201837605926645913172265917457221⟩,
  ⟨-12225818264640589241877463192217915142246016865961, 18877611168794216687978810945147341993001134754524⟩,
  ⟨11020772493985486708408180544541300993296442571473, -18575926817637757065132150997810954134467170199670⟩,
  ⟨-9771947274866679275717590600515757288274548057053, 19262178743736295571085234553824060004675834481178⟩,
  ⟨13235876257435116800762050733039601440906489152314, -2370995995621147079661971922456927559785630338723⟩,
  ⟨5094762835459208645300398230685595603180216280894, 12444011972182033918690215204842960320959093939402⟩,
  ⟨-7311882374434337497518021797309486015994190049252, 19314633368564067671598302787313622086664248783805⟩,
  ⟨12383974821914466223571663311743389874142824374494, -16527427314310011323039525729666973368745548128824⟩,
  ⟨-4888094841873266134669071053927600753064134918010, 19030271389185425219656410382049165818338735525175⟩,
  ⟨13443409589174740842164543166274418297678423248050, -14328972012914325953353170260850340371318866996977⟩,
  ⟨14131664563744353291215105220726285298079730277808, -4770172592853437778276256702203545512883670472775⟩,
  ⟨3549800752303474806706263380238597332371707126145, 14486455899451171724798009443273368291282646164542⟩,
  ⟨14174095439063570318732797656337715808332186520073, -12016296139673446182761964465751153468403698611363⟩,
  ⟨-2544143310887466985335416266006486654052345838691, 18407164073959905587453200693097860074162046250345⟩,
  ⟨14549251279562298259346663372295523769319753286312, -7199096170594152989739656134323494468447165611504⟩,
  ⟨1723348280932745224501837291942101211636608693414, 16141182396959484298328819594681027951289892349637⟩,
  ⟨-324785513731065982089572428678468947618010897778, 17444784047958762671029092352545249327991363579334⟩,
  ⟨14551591069338200224256927659485331058535835495179, -9626898434106532146757486157394507226535438215189⟩
]

def pt (j : Nat) : GZ := nth pts j

def psum (k : Nat) : Nat → GZ
  | 0 => ⟨0, 0⟩
  | m + 1 => GZ.add (psum k m) (GZ.pw (pt m) k)

theorem bir_ok : pt 0 = ⟨S, 0⟩ := by first | decide +kernel | decide

theorem nokta_ok : ∀ j, j < 50 → S * S ≤ (pt j).nsq := by first | decide +kernel | decide

theorem toplam_ok : ∀ m, m < 50 →
    (psum (m + 2) 50).nsq * (BDEN * BDEN) ≤ (BNUM * BNUM) * ipow S (2 * (m + 2)) := by first | decide +kernel | decide

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

/-- Ana teorem: Δ*_50 ≤ 0.12709904148206 (|z|² = normSq z biçiminde, bölmesiz). -/
theorem ust_sinir :
    ∃ z : ℕ → ℂ, z 0 = 1 ∧ (∀ j, j < 50 → 1 ≤ Complex.normSq (z j)) ∧
      (∀ k, 2 ≤ k → k ≤ 51 →
        Complex.normSq (∑ j ∈ Finset.range 50, z j ^ k) * ((BDEN : ℝ) ^ 2) ≤ (BNUM : ℝ) ^ 2) := by
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
    have hm : m < 50 := by omega
    have hsum : (∑ j ∈ Finset.range 50, ((pt j).toC * (r : ℂ)) ^ (m + 2))
        = (psum (m + 2) 50).toC * ((r ^ (m + 2) : ℝ) : ℂ) := by
      rw [toC_psum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_pow, Complex.ofReal_pow]
    show Complex.normSq (∑ j ∈ Finset.range 50, ((pt j).toC * (r : ℂ)) ^ (m + 2)) * ((BDEN : ℝ) ^ 2)
        ≤ (BNUM : ℝ) ^ 2
    rw [hsum, Complex.normSq_mul, normSq_toC, Complex.normSq_ofReal]
    have h3 : (((psum (m + 2) 50).nsq * (BDEN * BDEN) : Int) : ℝ)
        ≤ (((BNUM * BNUM) * ipow S (2 * (m + 2)) : Int) : ℝ) := by exact_mod_cast toplam_ok m hm
    push_cast at h3
    rw [ipow_cast] at h3
    calc ((psum (m + 2) 50).nsq : ℝ) * (r ^ (m + 2) * r ^ (m + 2)) * (BDEN : ℝ) ^ 2
        = (((psum (m + 2) 50).nsq : ℝ) * ((BDEN : ℝ) * BDEN)) * (r ^ (m + 2) * r ^ (m + 2)) := by ring
      _ ≤ ((BNUM : ℝ) * BNUM * (S : ℝ) ^ (2 * (m + 2))) * (r ^ (m + 2) * r ^ (m + 2)) :=
          mul_le_mul_of_nonneg_right h3 (mul_self_nonneg _)
      _ = (BNUM : ℝ) ^ 2 * ((S : ℝ) * r) ^ (2 * (m + 2)) := by ring
      _ = (BNUM : ℝ) ^ 2 := by rw [hSr, one_pow, mul_one]

end

end Turan973.N50

#print axioms Turan973.N50.ust_sinir

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

/-- L1 + L2: Δ*_50 ≤ BNUM / BDEN (= 0.12709904148206). -/
theorem N50_DeltaStar : Turan973.L2.DeltaStar 50 ≤ (Turan973.N50.BNUM : ℝ) / (Turan973.N50.BDEN : ℝ) := by
  have hD : (0 : ℝ) < (Turan973.N50.BDEN : ℝ) := by
    first
    | exact_mod_cast (show (0 : Int) < Turan973.N50.BDEN by decide)
    | (unfold Turan973.N50.BDEN; norm_num)
    | (norm_num [Turan973.N50.BDEN])
  have hN : (0 : ℝ) ≤ (Turan973.N50.BNUM : ℝ) := by
    first
    | exact_mod_cast (show (0 : Int) ≤ Turan973.N50.BNUM by decide)
    | (norm_num [Turan973.N50.BNUM])
  obtain ⟨z, h0, h1, h2⟩ := Turan973.N50.ust_sinir
  refine Turan973.L2.DeltaStar_le 50 _ (div_nonneg hN hD.le) ⟨z, h0, h1, fun k hk1 hk2 => ?_⟩
  have h := h2 k hk1 (by omega)
  have hD2 : (0 : ℝ) < (Turan973.N50.BDEN : ℝ) ^ 2 := pow_pos hD 2
  first
  | (rw [div_pow, le_div_iff₀ hD2]; exact h)
  | (rw [div_pow]; exact (le_div_iff₀ hD2).mpr h)
  | (rw [div_pow, le_div_iff hD2]; exact h)

end Turan973.Birlesim

#print axioms Turan973.L2.DeltaStar_le
#print axioms Turan973.Birlesim.N50_DeltaStar
