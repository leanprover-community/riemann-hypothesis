import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpenLeIsCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.FinsumQuotLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMaximalCompactOpenCompact

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.Psmall

section Generic

variable {P X : Type} [Group P] [Group X]

theorem hint_smul (K : Subgroup P) (c : ℂ) (v : P → ℂ) : hint K (fun m => c * v m) = c * hint K v := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    exact GlobalTheory.CompanionTheory.FamClP.hint_zero K
  · have hst : rStab (fun m => c * v m) = rStab v := by
      ext r
      show (∀ x, c * v (x * r) = c * v x) ↔ ∀ x, v (x * r) = v x
      exact forall_congr' fun x => mul_right_inj' hc
    unfold hint
    rw [hst, show (∑ᶠ q : P ⧸ (rStab v ⊓ K), c * v q.out) = c * ∑ᶠ q : P ⧸ (rStab v ⊓ K), v q.out from
      (smul_finsum c _).symm]
    ring

theorem act_left (K L : Subgroup P) (c : ℂ) (φ : P →* X) (G : X → ℂ) (z : X) (l : P) (hl : l ∈ L) :
    hint K (fun m => (L : Set P).indicator (fun _ => c) m * G (z * φ l * φ m)) =
      hint K (fun m => (L : Set P).indicator (fun _ => c) m * G (z * φ m)) := by
  rw [← GlobalTheory.CompanionTheory.FamClP.hint_left K (fun m => (L : Set P).indicator (fun _ => c) m * G (z * φ m)) l]
  congr 1
  funext m
  have hmem : l * m ∈ L ↔ m ∈ L :=
    ⟨fun h => by simpa using L.mul_mem (L.inv_mem hl) h, fun h => L.mul_mem hl h⟩
  simp only [Set.indicator_apply, SetLike.mem_coe, hmem, map_mul, mul_assoc]

theorem idem_fix_iff (K L : Subgroup P) (hLK : L ≤ K) (hfin : L.relIndex K ≠ 0) (φ : P →* X) (G : X → ℂ) :
    (fun z => hint K (fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ)) m * G (z * φ m))) = G ↔
      ∀ l ∈ L, ∀ z, G (z * φ l) = G z := by
  constructor
  · intro h l hl z
    have h1 := congrFun h (z * φ l)
    have h2 := congrFun h z
    rw [← h1, ← h2]
    exact act_left K L _ φ G z l hl
  · intro h
    funext z
    have hu : (fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ)) m * G (z * φ m)) =
        fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ) * G z) m := by
      funext m
      by_cases hm : m ∈ L
      · simp [hm, h m hm z]
      · simp [hm]
    rw [hu]
    have hst : L ≤ rStab (fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ) * G z) m) := by
      intro l hl x
      have : x * l ∈ L ↔ x ∈ L :=
        ⟨fun h' => by simpa using L.mul_mem h' (L.inv_mem hl), fun h' => L.mul_mem h' hl⟩
      simp only [Set.indicator_apply, SetLike.mem_coe, this]
    rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level P K L _ hLK hst hfin]
    have hone : ((((1 : P) : P ⧸ L)).out) ∈ L := by
      have := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : P) : P ⧸ L))
      simpa using this
    rw [finsum_eq_single _ ((1 : P) : P ⧸ L)]
    · simp only [Set.indicator_apply, SetLike.mem_coe, hone, if_true]
      have hc : ((L.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hfin
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    · intro q hq
      have : q.out ∉ L := by
        intro hin
        apply hq
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using hin)
      simp [this]

end Generic

section Generic2

variable {P X : Type} [Group P] [Group X]

theorem hecke_eq [TopologicalSpace P] [IsTopologicalGroup P] (K : Subgroup P) (hK : IsOpen (K : Set P)) (φ : P →* X)
    (f : P → ℂ) (G : X → ℂ) (hf : HasCompactSupport f) (hfK : ∀ k ∈ K, ∀ g, f (g * k) = f g)
    (hG : ∀ k ∈ K, ∀ z, G (z * φ k) = G z) :
    (fun z => hint K (fun m => f m * G (z * φ m))) = heckeVec ((rightReg ℂ X ℂ).comp φ) K f G := by
  funext z
  have hst : K ≤ rStab (fun m => f m * G (z * φ m)) := by
    intro k hk x
    show f (x * k) * G (z * φ (x * k)) = f x * G (z * φ x)
    rw [hfK k hk, map_mul, ← mul_assoc, hG k hk]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level P K K _ le_rfl hst (by simp), Subgroup.relIndex_self, Nat.cast_one, inv_one,
    one_mul]
  have hfin : (Function.support fun c : P ⧸ K => f c.out • ((rightReg ℂ X ℂ).comp φ) c.out G).Finite :=
    (GlobalTheory.TwTrLin.finite_out_support hK hf).subset (Function.support_smul_subset_left (fun c : P ⧸ K => f c.out)
      (fun c : P ⧸ K => ((rightReg ℂ X ℂ).comp φ) c.out G))
  unfold heckeVec
  rw [finsum_apply hfin]
  rfl

end Generic2

end PositivityTheory.Rg.BcB.F.FA.Psmall

namespace PositivityTheory.Rg.BcB.F.FA

open Psmall in
theorem actIdem_holds : ActIdem := by
  intro E _ _ _ a b w L G hL hLK _
  have hK : IsCompact ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  have hfin : L.relIndex (K2 a b w) ≠ 0 := GlobalTheory.relIndex_ne_zero_of_isOpen_le_isCompact _ _ hK hL hLK
  constructor
  · rw [GlobalTheory.TwTrLin.mem_fixed_iff]
    exact (idem_fix_iff (K2 a b w) L hLK hfin ((embW a w).prodMap (embW b w)) G).trans
      ⟨fun h l hl => funext (h l hl), fun h l hl z => congrFun (h l hl) z⟩
  · rw [GlobalTheory.TwTrLin.mem_fixed_iff]
    exact (idem_fix_iff (K2 a b w) L hLK hfin ((embT a w).prodMap (embT b w)) G).trans
      ⟨fun h l hl => funext (h l hl), fun h l hl z => congrFun (h l hl) z⟩

end PositivityTheory.Rg.BcB.F.FA

namespace PositivityTheory.Rg.BcB.F.Tail

open PositivityTheory.Rg.BcB.F.FA.Psmall in
theorem actHecke_holds : ActHecke := by
  intro E _ _ _ a b w f G hf hfK
  have hK : IsOpen ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  constructor
  · intro hG
    rw [GlobalTheory.TwTrLin.mem_fixed_iff] at hG
    exact hecke_eq (K2 a b w) hK ((embW a w).prodMap (embW b w)) f G hf hfK fun k hk z => congrFun (hG k hk) z
  · intro hG
    rw [GlobalTheory.TwTrLin.mem_fixed_iff] at hG
    exact hecke_eq (K2 a b w) hK ((embT a w).prodMap (embT b w)) f G hf hfK fun k hk z => congrFun (hG k hk) z

namespace Psmall

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem actP_smul_fun (w : Pl E) (c : ℂ) (u : GLw a w × GLw b w → ℂ) (G : H E a b → ℂ) :
    actP w (c • u) G = c • actP w u G := by
  funext z
  show hint _ (fun m => (c • u) m * _) = c * hint _ _
  rw [← PositivityTheory.Rg.BcB.F.FA.Psmall.hint_smul]
  congr 1
  funext m
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem actP_smul_vec (w : Pl E) (c : ℂ) (u : GLw a w × GLw b w → ℂ) (G : H E a b → ℂ) :
    actP w u (c • G) = c • actP w u G := by
  funext z
  show hint _ (fun m => u m * pairRt a b w m (c • G) z) = c * hint _ _
  rw [← PositivityTheory.Rg.BcB.F.FA.Psmall.hint_smul]
  congr 1
  funext m
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem actP_zero (w : Pl E) (G : H E a b → ℂ) : actP w (0 : GLw a w × GLw b w → ℂ) G = 0 := by
  funext z
  show hint _ (fun m => (0 : GLw a w × GLw b w → ℂ) m * _) = 0
  simp only [Pi.zero_apply, zero_mul]
  exact GlobalTheory.CompanionTheory.FamClP.hint_zero _

theorem locM_iter_smul (w : Pl E) {k : Type} [Fintype k] (c : ℂ) (M : k → k → GLw a w × GLw b w → ℂ)
    (G : k → H E a b → ℂ) (m : ℕ) :
    (locM w fun x y => c • M x y)^[m] G = c ^ m • (locM w M)^[m] G := by
  have h1 : ∀ Y : k → H E a b → ℂ, (locM w fun x y => c • M x y) Y = c • locM w M Y := by
    intro Y
    funext x
    simp only [locM, actP_smul_fun, Pi.smul_apply, Finset.smul_sum]
  have h2 : ∀ (d : ℂ) (Y : k → H E a b → ℂ), locM w M (d • Y) = d • locM w M Y := by
    intro d Y
    funext x
    simp only [locM, Pi.smul_apply, actP_smul_vec, Finset.smul_sum]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, h1, h2, smul_smul, pow_succ']

theorem locM_iter_diag (w : Pl E) {k : Type} [Fintype k] (q : k → GLw a w × GLw b w → ℂ)
    (G : k → H E a b → ℂ) (m : ℕ) (x : k) :
    (locM w fun x y => if x = y then q x else 0)^[m] G x = (actP w (q x))^[m] (G x) := by
  have h1 : ∀ (Y : k → H E a b → ℂ) (x : k), (locM w fun x y => if x = y then q x else 0) Y x = actP w (q x) (Y x) := by
    intro Y x
    show ∑ y, actP w (if x = y then q x else 0) (Y y) = _
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      rw [if_neg (Ne.symm hy), actP_zero]
    · intro h
      exact absurd (Finset.mem_univ x) h
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1, ih]

end Psmall

open Psmall in
theorem locPow_holds : LocPow := by
  intro E _ _ _ a b w k _ U G m _ _
  constructor
  · intro c M hne h0
    apply hne
    rw [locM_iter_smul, h0, smul_zero]
  · intro q hne
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hne
    funext x
    rw [locM_iter_diag]
    exact hall x

end PositivityTheory.Rg.BcB.F.Tail
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

section Gen

set_option linter.unusedSectionVars false

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [FirstCountableTopology Γ] [LocallyCompactSpace Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (ν : Measure Γ) [ν.IsHaarMeasure]

theorem cont_of_rinv {f : Γ → ℂ} {U : Subgroup Γ} (hU : IsOpen (U : Set Γ)) (hf : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  refine (continuousAt_const (y := f g)).congr ?_
  have hm : {y : Γ | g⁻¹ * y ∈ U} ∈ 𝓝 g :=
    (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [U.one_mem])
  filter_upwards [hm] with y hy
  have := hf _ hy g
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem cont_convL {φ₁ φ₂ : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂) :
    Continuous fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
  have e : (fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) = fun g => ∫ h in tsupport φ₁, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
    funext g
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hh, zero_mul]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ s₁.isCompact
  exact (h₁.comp continuous_snd).mul (h₂.comp (continuous_snd.inv.mul continuous_fst))

theorem supp_convL {φ₁ φ₂ : Γ → ℂ} (s₁ : HasCompactSupport φ₁) (s₂ : HasCompactSupport φ₂) :
    HasCompactSupport fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
  refine HasCompactSupport.intro (s₁.isCompact.mul s₂.isCompact) fun g hg => ?_
  have : ∀ h, φ₁ h * φ₂ (h⁻¹ * g) = 0 := by
    intro h
    by_cases h1 : h ∈ tsupport φ₁
    · have h2 : h⁻¹ * g ∉ tsupport φ₂ := fun h2 => hg (Set.mem_mul.2 ⟨h, h1, h⁻¹ * g, h2, mul_inv_cancel_left h g⟩)
      rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  simp [this]

theorem cont_convR {φ₂ f : Γ → ℂ} (h₂ : Continuous φ₂) (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Continuous fun h => ∫ k, φ₂ k * f (h * k) ∂ν := by
  have e : (fun h => ∫ k, φ₂ k * f (h * k) ∂ν) = fun h => ∫ k in tsupport φ₂, φ₂ k * f (h * k) ∂ν := by
    funext h
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hk, zero_mul]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ s₂.isCompact
  exact (h₂.comp continuous_snd).mul (hf.comp (continuous_fst.mul continuous_snd))

theorem int_L {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Integrable (fun g => (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g) ν :=
  ((cont_convL ν h₁ s₁ h₂).mul hf).integrable_of_hasCompactSupport ((supp_convL ν s₁ s₂).mul_right)

theorem int_R {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Integrable (fun h => φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν) ν :=
  (h₁.mul (cont_convR ν h₂ s₂ hf)).integrable_of_hasCompactSupport s₁.mul_right

theorem swap_key {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    ∫ g, (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g ∂ν = ∫ h, φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν ∂ν := by
  have hc : Continuous (Function.uncurry fun g h : Γ => φ₁ h * φ₂ (h⁻¹ * g) * f g) :=
    ((h₁.comp continuous_snd).mul (h₂.comp (continuous_snd.inv.mul continuous_fst))).mul (hf.comp continuous_fst)
  have hs : HasCompactSupport (Function.uncurry fun g h : Γ => φ₁ h * φ₂ (h⁻¹ * g) * f g) := by
    refine HasCompactSupport.intro ((s₁.isCompact.mul s₂.isCompact).prod s₁.isCompact) fun p hp => ?_
    show φ₁ p.2 * φ₂ (p.2⁻¹ * p.1) * f p.1 = 0
    by_cases h1 : p.2 ∈ tsupport φ₁
    · have h2 : p.2⁻¹ * p.1 ∉ tsupport φ₂ := fun h2 =>
        hp ⟨Set.mem_mul.2 ⟨p.2, h1, p.2⁻¹ * p.1, h2, mul_inv_cancel_left p.2 p.1⟩, h1⟩
      rw [image_eq_zero_of_notMem_tsupport h2, mul_zero, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
  calc ∫ g, (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g ∂ν
      = ∫ g, ∫ h, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ h, ∫ g, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν ∂ν := integral_integral_swap_of_hasCompactSupport hc hs
    _ = ∫ h, φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        have e1 := integral_mul_left_eq_self (μ := ν) (fun g => φ₂ (h⁻¹ * g) * f g) h
        simp only [inv_mul_cancel_left] at e1
        show ∫ g, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν = φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν
        rw [e1, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        show φ₁ h * φ₂ (h⁻¹ * g) * f g = φ₁ h * (φ₂ (h⁻¹ * g) * f g)
        ring

end Gen

theorem finH_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (g h : Hf E a b) :
    finH (g * h) = finH g * finH h := by
  simp [finH, map_mul]

attribute [local instance] borelG borelF borelH

theorem convMul_holds : Tail.ConvMul := by
  intro E _ _ _ B A ψ ψ' U F hψ hψ' hU hF
  have := B.hν
  have : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  refine ⟨?_, ?_⟩
  · funext i X
    obtain ⟨p, x₀⟩ := i
    have hfc : ∀ z, Continuous fun g => F (p, z) (X * finH g) := by
      intro z
      refine cont_of_rinv hU fun u hu g => ?_
      rw [finH_mul', ← mul_assoc, hF _ u hu]
    simp only [convF, mulF]
    calc ∑ z, ∫ g, (∑ w, ∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν
        = ∑ z, ∑ w, ∫ g, (∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν := by
          refine Finset.sum_congr rfl fun z _ => ?_
          simp_rw [Finset.sum_mul]
          exact integral_finsetSum _ fun w _ =>
            int_L B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)
      _ = ∑ w, ∑ z, ∫ g, (∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν :=
          Finset.sum_comm
      _ = ∑ w, ∑ z, ∫ h, ψ x₀ w h * ∫ k, ψ' w z k * F (p, z) (X * finH h * finH k) ∂B.ν ∂B.ν := by
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
          rw [swap_key B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)]
          simp only [finH_mul', mul_assoc]
      _ = ∑ w, ∫ h, ψ x₀ w h * ∑ z, ∫ k, ψ' w z k * F (p, z) (X * finH h * finH k) ∂B.ν ∂B.ν := by
          refine Finset.sum_congr rfl fun w _ => ?_
          simp_rw [Finset.mul_sum]
          refine (integral_finsetSum _ fun z _ => ?_).symm
          have := int_R B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)
          simpa only [finH_mul', mul_assoc] using this
  · intro hψU i u hu x
    simp only [convF]
    refine Finset.sum_congr rfl fun z _ => ?_
    have e := integral_mul_left_eq_self (μ := B.ν) (fun k => ψ' i.2 z k * F (i.1, z) (x * finH k)) u
    simp only [hψU _ _ u hu, finH_mul', ← mul_assoc] at e
    exact e

theorem fmOneOf_holds : FmOneOf := by
  intro hOff hIdem E _ _ _ κ _ S P B e hS hP U₁ U₂ L A F w₀ hU₁ hU₂ hL hD hF hw₀
  have hLev : ∀ i, HasLev (F i) := fun i => (hF i).1

  have hxy : ∀ x y : B.κ, (∀ w : P, e x w = e y w) → x = y := fun x y h => e.injective (funext h)

  have hent : ∀ (x : B.κ) (w : Pl E), (w ∉ P → L.s w = idem (U₁ w)) → L.ent P (e x) (e x) w = idem (U₁ w) := by
    intro x w hw
    unfold LM.ent
    split_ifs with h
    · rw [hD w h]; simp
    · exact hw h
  have hP1 : ∀ (w : Pl E) (G : H E B.a B.b → ℂ), w ∈ S → HasLev G → G ∈ fixed (pairRt B.a B.b w) (U₁ w) →
      actP w (idem (U₁ w)) G = G := fun w G _ hG hfx =>
    ((hIdem E B.a B.b w (U₁ w) G (hU₁.1 w).1 (hU₁.1 w).2 hG).1).2 hfx
  have hT1 : ∀ (w : Pl E) (G : H E B.a B.b → ℂ), HasLev G → G ∈ fixed (pairRtT B.a B.b w) (U₂ w) →
      actT w (idem (U₂ w)) G = G := fun w G hG hfx =>
    ((hIdem E B.a B.b w (U₂ w) G (hU₂.1 w).1 (hU₂.1 w).2 hG).2).2 hfx
  refine ⟨fun hw₀P hs ht i => ?_, fun hsp hs ht i => ?_⟩
  · have hne : ∀ w ∈ P, ∀ h : w ∈ S, (Sum.inl ⟨w₀, hw₀⟩ : Slot S) ≠ Sum.inl ⟨w, h⟩ := by
      intro w hwP h heq
      have : w₀ = w := congrArg Subtype.val (Sum.inl_injective heq)
      exact hw₀P (this ▸ hwP)
    have hQ : Quiet S P B e L (Sum.inl ⟨w₀, hw₀⟩) F := by
      refine ⟨fun w hwP hw x y hxy' => ?_, fun j hj p x y hxe => ?_⟩
      · rw [hD w hwP, if_neg hxy']
      · have hx : x = y := hxy x y fun w => hxe w fun h => hne w.1 w.2 h
        subst hx
        rcases j with ⟨w, hwS⟩ | ⟨w, hwS, hwsp⟩
        · have hww : w ≠ w₀ := fun h => hj (by subst h; rfl)
          show actP w (L.ent P (e x) (e x) w) (F (p, x)) = F (p, x)
          rw [hent x w fun _ => hs w hww]
          exact hP1 w _ hwS (hLev _) ((hF _).2 w hwS).1
        · show actT w (L.t w) (F (p, x)) = F (p, x)
          rw [ht w]
          exact hT1 w _ (hLev _) (((hF _).2 w hwS).2 hwsp)
    obtain ⟨p, x⟩ := i
    exact hOff E κ S P B e hS hP A L (Sum.inl ⟨w₀, hw₀⟩) F hL hLev hne hQ p x
  · have hne : ∀ w ∈ P, ∀ h : w ∈ S, (Sum.inr ⟨w₀, hw₀, hsp⟩ : Slot S) ≠ Sum.inl ⟨w, h⟩ := by
      intro w _ h heq
      cases heq
    have hQ : Quiet S P B e L (Sum.inr ⟨w₀, hw₀, hsp⟩) F := by
      refine ⟨fun w hwP hw x y hxy' => ?_, fun j hj p x y hxe => ?_⟩
      · rw [hD w hwP, if_neg hxy']
      · have hx : x = y := hxy x y fun w => hxe w fun h => hne w.1 w.2 h
        subst hx
        rcases j with ⟨w, hwS⟩ | ⟨w, hwS, hwsp⟩
        · show actP w (L.ent P (e x) (e x) w) (F (p, x)) = F (p, x)
          rw [hent x w fun _ => hs w]
          exact hP1 w _ hwS (hLev _) ((hF _).2 w hwS).1
        · have hww : w ≠ w₀ := fun h => hj (by subst h; rfl)
          show actT w (L.t w) (F (p, x)) = F (p, x)
          rw [ht w hww]
          exact hT1 w _ (hLev _) (((hF _).2 w hwS).2 hwsp)
    obtain ⟨p, x⟩ := i
    exact hOff E κ S P B e hS hP A L (Sum.inr ⟨w₀, hw₀, hsp⟩) F hL hLev hne hQ p x

end PositivityTheory.Rg.BcB.F.FA

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

attribute [local instance] borelG borelF borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {κ : Pl E → Type} [∀ w, Fintype (κ w)]
  {S : Set (Pl E)} {P : Finset (Pl E)} {B : Block E} {e : B.κ ≃ ∀ w : P, κ w}

theorem fm_term_zero (hP : (↑P : Set (Pl E)) ⊆ S) {L : LM κ B.a B.b} (hL : L.Ok P) (x z : B.κ) (w : P)
    (hw : L.m w.1 (e x w) (e z w) = 0) (G : H E B.a B.b → ℂ) (y : H E B.a B.b) :
    ∫ h, fm S P B e L x z h * G (y * finH h) ∂B.ν = 0 := by
  have h0 : ∀ h, finFn S (L.ent P (e x) (e z)) L.t h = 0 := by
    intro h
    by_contra hne
    apply (GlobalTheory.CompanionTheory.FinTestTw.factors_ne_zero (hL.1 _ _) hL.2 hne w.1 (hP w.2)).1
    simp only [LM.ent, dif_pos w.2]
    exact congrFun hw _
  simp [fm, h0]

theorem fm_term_act (hS : IsSection S) (hFC : FinConv) (hFA : FinAct) {L : LM κ B.a B.b} (hL : L.Ok P) (x z : B.κ)
    (i₀ : Slot S) (G : H E B.a B.b → ℂ) (hG : HasLev G)
    (hfix : ∀ i, i ≠ i₀ → actS (L.ent P (e x) (e z)) L.t i G = G) (y : H E B.a B.b) :
    ∫ h, fm S P B e L x z h * G (y * finH h) ∂B.ν = actS (L.ent P (e x) (e z)) L.t i₀ G y := by
  have hv : B.vol ≠ 0 := (hFC E B S hS).1
  have key := hFA E B S hS (L.ent P (e x) (e z)) L.t (hL.1 _ _) hL.2 G hG [i₀] (List.nodup_singleton _)
    (fun i hi => hfix i (by simpa using hi)) y
  simp only [List.foldr_cons, List.foldr_nil] at key
  simp only [fm, mul_assoc]
  rw [integral_const_mul, key, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

end

theorem fmAtP_holds : FmAtPOf := by
  intro hFC hFA E _ _ _ κ _ S P B e hS hP A L w₀ F hL hF hQ p x
  funext y
  set g : κ w₀ → B.κ := fun t => e.symm (Function.update (e x) w₀ t) with hg
  have hginj : Function.Injective g := by
    intro t t' h
    have := congrArg (fun z => e z w₀) h
    simpa [hg] using this
  have hterm : ∀ z : B.κ, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν =
      ∑ t : κ w₀, if z = g t then actP w₀.1 (L.m w₀ (e x w₀) t) (F (p, g t)) y else 0 := by
    intro z
    by_cases hz : ∃ t, z = g t
    · obtain ⟨t, rfl⟩ := hz
      rw [Finset.sum_eq_single t (fun t' _ ht' => if_neg fun h => ht' (hginj h).symm) (by simp), if_pos rfl]
      have hez : e (g t) = Function.update (e x) w₀ t := by simp [hg]
      rw [fm_term_act hS hFC hFA hL x (g t) (Sum.inl ⟨w₀.1, hP w₀.2⟩) (F (p, g t)) (hF _) ?_ y]
      · simp only [actS, LM.ent]
        rw [hez]
        simp
      · intro i hi
        refine hQ.2 i hi p x (g t) fun w hw => ?_
        rw [hez]
        have hne : w ≠ w₀ := by
          rintro rfl
          exact hw (hP w.2) rfl
        rw [Function.update_of_ne hne]
    · rw [Finset.sum_eq_zero fun t _ => if_neg fun h => hz ⟨t, h⟩]
      have : ∃ w : P, w ≠ w₀ ∧ e x w ≠ e z w := by
        by_contra hall
        push Not at hall
        apply hz
        refine ⟨e z w₀, e.injective ?_⟩
        simp only [hg, Equiv.apply_symm_apply]
        funext w
        by_cases hw : w = w₀
        · subst hw; simp
        · rw [Function.update_of_ne hw]; exact (hall w hw).symm
      obtain ⟨w, hw, hne⟩ := this
      refine fm_term_zero hP hL x z w ?_ _ y
      refine hQ.1 w.1 w.2 (fun h hh => ?_) _ _ hne
      apply hw
      apply Subtype.ext
      have := congrArg Slot.pl hh
      simpa [Slot.pl] using this.symm
  show ∑ z, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = _
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_comm]
  simp [Finset.sum_ite_eq', hg]

theorem fmOff_holds : FmOffOf := by
  intro hFC hFA E _ _ _ κ _ S P B e hS hP A L i₀ F hL hF hoff hQ p x
  funext y
  show ∑ z, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = _
  rw [Finset.sum_eq_single x]
  · rw [fm_term_act hS hFC hFA hL x x i₀ (F (p, x)) (hF _) (fun i hi => hQ.2 i hi p x x fun _ _ => rfl) y]
    rcases i₀ with ⟨w, hw⟩ | ⟨w, hw⟩
    · have hwP : w ∉ P := fun h => hoff w h hw rfl
      simp [actS, LM.ent, dif_neg hwP]
    · rfl
  · intro z _ hz
    have : ∃ w : P, e x w ≠ e z w := by
      by_contra hall
      push Not at hall
      exact hz (e.injective (funext hall)).symm
    obtain ⟨w, hne⟩ := this
    exact fm_term_zero hP hL x z w (hQ.1 w.1 w.2 (hoff w.1 w.2) _ _ hne) _ y
  · simp

end PositivityTheory.Rg.BcB.F.FA

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem relIndex_ne {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} (hV : IsOpen (V : Set (GLw a w × GLw b w)))
    (hle : V ≤ K2 a b w) : V.relIndex (K2 a b w) ≠ 0 := by
  have hK : IsCompact ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    have := (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a).prod (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w b)
    simpa [K2, Subgroup.coe_prod] using this
  exact GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hV hK

theorem idem_left {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} {v : GLw a w × GLw b w} (hv : v ∈ V)
    (g0 : GLw a w × GLw b w) : idem V (v * g0) = idem V g0 := by
  unfold idem
  by_cases hg : g0 ∈ V
  · rw [Set.indicator_of_mem (V.mul_mem hv hg), Set.indicator_of_mem hg]
  · have : v * g0 ∉ V := fun h => hg (by simpa using V.mul_mem (V.inv_mem hv) h)
    rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]

theorem idem_right {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} {v : GLw a w × GLw b w} (hv : v ∈ V)
    (g0 : GLw a w × GLw b w) : idem V (g0 * v) = idem V g0 := by
  unfold idem
  by_cases hg : g0 ∈ V
  · rw [Set.indicator_of_mem (V.mul_mem hg hv), Set.indicator_of_mem hg]
  · have : g0 * v ∉ V := fun h => hg (by simpa using V.mul_mem h (V.inv_mem hv))
    rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]

theorem mconv_zero_left {w : Pl E} (f : GLw a w × GLw b w → ℂ) :
    mconv (fun _ => (0 : ℂ)) f = fun _ => 0 := by
  funext m
  unfold mconv
  simpa using FinConv.hint_zero ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))

theorem mconv_zero_right {w : Pl E} (f : GLw a w × GLw b w → ℂ) :
    mconv f (fun _ => (0 : ℂ)) = fun _ => 0 := by
  funext m
  unfold mconv
  simpa using FinConv.hint_zero ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))

theorem mconv_left {w : Pl E} {f g : GLw a w × GLw b w → ℂ} {v : GLw a w × GLw b w} (hf : ∀ x, f (v * x) = f x)
    (m : GLw a w × GLw b w) : mconv f g (v * m) = mconv f g m := by
  unfold mconv
  calc hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (fun m' => f m' * g (m'⁻¹ * (v * m)))
      = hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
          (fun z => (fun z => f (v * z) * g (z⁻¹ * m)) (v⁻¹ * z)) := by
        congr 1; funext z; simp [mul_assoc]
    _ = hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (fun z => f (v * z) * g (z⁻¹ * m)) :=
        FinConv.hint_left _ (fun z => f (v * z) * g (z⁻¹ * m)) v⁻¹
    _ = _ := by congr 1; funext z; rw [hf]

theorem mconv_right {w : Pl E} {f g : GLw a w × GLw b w → ℂ} {v : GLw a w × GLw b w} (hg : ∀ x, g (x * v) = g x)
    (m : GLw a w × GLw b w) : mconv f g (m * v) = mconv f g m := by
  unfold mconv
  congr 1; funext z; rw [← mul_assoc, hg]

theorem mconv_idem_left {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} (hV : IsOpen (V : Set (GLw a w × GLw b w)))
    (hle : V ≤ K2 a b w) {f : GLw a w × GLw b w → ℂ} (hf : ∀ v ∈ V, ∀ x, f (v * x) = f x) :
    mconv (idem V) f = f := by
  funext m
  have hr := relIndex_ne hV hle
  set u : GLw a w × GLw b w → ℂ := fun m' => idem V m' * f (m'⁻¹ * m) with hu
  have hSu : V ≤ rStab u := by
    intro k hk x
    simp only [hu]
    rw [idem_right hk, _root_.mul_inv_rev, mul_assoc, hf _ (V.inv_mem hk)]
  have hsupp : ∀ q : (GLw a w × GLw b w) ⧸ V, q ≠ QuotientGroup.mk 1 → u q.out = 0 := by
    intro q hq
    simp only [hu]
    have : q.out ∉ V := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 (by simpa using V.inv_mem hm)
    unfold idem
    rw [Set.indicator_of_notMem this, zero_mul]
  have hfin : (Function.support fun q : (GLw a w × GLw b w) ⧸ V => u q.out).Finite := by
    refine (Set.finite_singleton (QuotientGroup.mk 1 : (GLw a w × GLw b w) ⧸ V)).subset fun q hq => ?_
    by_contra hne
    exact hq (hsupp q hne)
  have h := PositivityTheory.Rg.BcN.F2.LocOpPf.hinteq (K2 a b w) V u hle hSu hr hfin
  change hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) u = f m
  rw [show ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) = K2 a b w from rfl, h,
    finsum_eq_single _ (QuotientGroup.mk 1) hsupp]
  obtain ⟨hh, e⟩ := QuotientGroup.mk_out_eq_mul V (1 : GLw a w × GLw b w)
  simp only [hu]
  rw [e, one_mul]
  unfold idem
  rw [Set.indicator_of_mem hh.2, hf _ (V.inv_mem hh.2)]
  have : ((V.relIndex (K2 a b w) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp

theorem mconv_idem_right {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} (hV : IsOpen (V : Set (GLw a w × GLw b w)))
    (hle : V ≤ K2 a b w) {f : GLw a w × GLw b w → ℂ} (hf : ∀ v ∈ V, ∀ x, f (x * v) = f x) :
    mconv f (idem V) = f := by
  funext m
  have hr := relIndex_ne hV hle
  set u : GLw a w × GLw b w → ℂ := fun m' => f m' * idem V (m'⁻¹ * m) with hu
  have hSu : V ≤ rStab u := by
    intro k hk x
    simp only [hu]
    rw [hf _ hk, _root_.mul_inv_rev, mul_assoc, idem_left (V.inv_mem hk)]
  have hsupp : ∀ q : (GLw a w × GLw b w) ⧸ V, q ≠ QuotientGroup.mk m → u q.out = 0 := by
    intro q hq
    simp only [hu]
    have : q.out⁻¹ * m ∉ V := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hm
    unfold idem
    rw [Set.indicator_of_notMem this, mul_zero]
  have hfin : (Function.support fun q : (GLw a w × GLw b w) ⧸ V => u q.out).Finite := by
    refine (Set.finite_singleton (QuotientGroup.mk m : (GLw a w × GLw b w) ⧸ V)).subset fun q hq => ?_
    by_contra hne
    exact hq (hsupp q hne)
  have h := PositivityTheory.Rg.BcN.F2.LocOpPf.hinteq (K2 a b w) V u hle hSu hr hfin
  change hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) u = f m
  rw [show ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) = K2 a b w from rfl, h,
    finsum_eq_single _ (QuotientGroup.mk m) hsupp]
  obtain ⟨hh, e⟩ := QuotientGroup.mk_out_eq_mul V m
  simp only [hu]
  rw [e, hf _ hh.2]
  unfold idem
  rw [Set.indicator_of_mem (by simpa using V.inv_mem hh.2)]
  have : ((V.relIndex (K2 a b w) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp

end PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem thL_cont_invol (n : ℕ) (w : Pl E) : Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := by
  unfold thL
  split_ifs
  · exact ⟨continuous_id, fun g => rfl⟩
  · exact ⟨GlobalTheory.LocTwist.continuous_thetaGL n (cj w) (GlobalTheory.CompanionTheory.IwUFacts.continuous_cj w),
      GlobalTheory.LocTwist.thetaGL_thetaGL n (cj w) (GlobalTheory.PrincCong.cj_cj w)⟩

theorem level_of_comap {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    (θ : G₁ →* G₁) (hθ : Continuous θ) (hθθ : ∀ g, θ (θ g) = g) (ι : G₁ →* G₂) (hι : Continuous ι)
    (U : Subgroup G₂) (hU : IsOpen (U : Set G₂)) (K : Subgroup G₁) (hK : ∀ g, ι g ∈ U → g ∈ K) :
    IsLevel θ K (U.comap ι ⊓ U.comap (ι.comp θ)) ∧ ∀ g ∈ U.comap ι ⊓ U.comap (ι.comp θ), ι g ∈ U := by
  refine ⟨⟨?_, fun g hg => hK g (Subgroup.mem_inf.1 hg).1, fun k hk => ?_⟩, fun g hg => (Subgroup.mem_inf.1 hg).1⟩
  · rw [Subgroup.coe_inf, Subgroup.coe_comap, Subgroup.coe_comap]
    exact (hU.preimage hι).inter (hU.preimage (hι.comp hθ))
  · obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨h2, ?_⟩
    change ι (θ (θ k)) ∈ U
    rw [hθθ]; exact h1

theorem exists_level_prod (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hle : U ≤ K2 a b w) :
    ∃ (V₁ : Subgroup (GLw a w)) (V₂ : Subgroup (GLw b w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) V₁ ∧
      IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) V₂ ∧ V₁.prod V₂ ≤ U := by
  obtain ⟨c₁, i₁⟩ := thL_cont_invol (E := E) a w
  obtain ⟨c₂, i₂⟩ := thL_cont_invol (E := E) b w
  have hl := level_of_comap (thL a w) c₁ i₁ (MonoidHom.inl (GLw a w) (GLw b w))
    (continuous_id.prodMk continuous_const) U hU (GlobalTheory.LFun.KGL w a)
    (fun g hg => (Subgroup.mem_prod.1 (hle hg)).1)
  have hr := level_of_comap (thL b w) c₂ i₂ (MonoidHom.inr (GLw a w) (GLw b w))
    (continuous_const.prodMk continuous_id) U hU (GlobalTheory.LFun.KGL w b)
    (fun g hg => (Subgroup.mem_prod.1 (hle hg)).2)
  refine ⟨_, _, hl.1, hr.1, fun x hx => ?_⟩
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_prod.1 hx
  have e : x = MonoidHom.inl (GLw a w) (GLw b w) x.1 * MonoidHom.inr (GLw a w) (GLw b w) x.2 := by
    ext <;> simp
  rw [e]
  exact U.mul_mem (hl.2 _ hx₁) (hr.2 _ hx₂)

theorem isHecke_idem {w : Pl E} (V₁ : Subgroup (GLw a w)) (V₂ : Subgroup (GLw b w))
    (hV₁ : IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) V₁) (hV₂ : IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) V₂) :
    IsHecke (V₁.prod V₂) (idem (V₁.prod V₂)) := by
  have hVo : IsOpen ((V₁.prod V₂ : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]; exact hV₁.1.prod hV₂.1
  have hVc : IsClosed ((V₁.prod V₂ : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) :=
    Subgroup.isClosed_of_isOpen _ hVo
  have hK : IsCompact ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [K2, Subgroup.coe_prod]
    exact (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a).prod (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w b)
  have hsub : ((V₁.prod V₂ : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) ⊆ (K2 a b w : Set _) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hx
    exact Subgroup.mem_prod.2 ⟨hV₁.2.1 h1, hV₂.2.1 h2⟩
  refine ⟨HasCompactSupport.intro' (hK.of_isClosed_subset hVc hsub) hVc fun x hx => ?_, fun k hk x => ⟨?_, ?_⟩⟩
  · unfold idem; exact Set.indicator_of_notMem hx _
  · unfold idem
    by_cases hx : x ∈ V₁.prod V₂
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((V₁.prod V₂).mul_mem hk hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (by simpa using (V₁.prod V₂).mul_mem ((V₁.prod V₂).inv_mem hk) h))]
  · unfold idem
    by_cases hx : x ∈ V₁.prod V₂
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((V₁.prod V₂).mul_mem hx hk)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (by simpa using (V₁.prod V₂).mul_mem h ((V₁.prod V₂).inv_mem hk)))]

end PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

set_option linter.unusedSectionVars false

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem fixed_mono {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {K K' : Subgroup G} (hle : K' ≤ K) {v : V} (hv : v ∈ fixed ρ K) : v ∈ fixed ρ K' := by
  simp only [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq] at hv ⊢
  intro h
  exact hv ⟨h.1, hle h.2⟩

theorem isHecke_zero {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) : IsHecke K (fun _ : G => (0 : ℂ)) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem isTestFunction_modify {φ ψ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (hφ : IsTestP φ) (T : Finset (Pl E))
    (V₁ : ∀ w : Pl E, Subgroup (GLw a w)) (V₂ : ∀ w : Pl E, Subgroup (GLw b w))
    (hV₁ : ∀ w, IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) (V₁ w)) (hV₂ : ∀ w, IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) (V₂ w))
    (hout : ∀ w, w ∉ T → ψ w = φ w) (hin : ∀ w ∈ T, IsHecke ((V₁ w).prod (V₂ w)) (ψ w)) : IsTestP ψ := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hT⟩ := hφ
  refine ⟨fun w => if w ∈ T then V₁ w else K₁ w, fun w => if w ∈ T then V₂ w else K₂ w, ⟨fun w => ?_, ?_⟩,
    ⟨fun w => ?_, ?_⟩, fun w => ?_, ?_⟩
  · by_cases h : w ∈ T
    · simp only [h, if_true]; exact hV₁ w
    · simp only [h, if_false]; exact hK₁.1 w
  · filter_upwards [hK₁.2, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hwT
    simp only [hwT, if_false, hw]
  · by_cases h : w ∈ T
    · simp only [h, if_true]; exact hV₂ w
    · simp only [h, if_false]; exact hK₂.1 w
  · filter_upwards [hK₂.2, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hwT
    simp only [hwT, if_false, hw]
  · by_cases h : w ∈ T
    · simp only [h, if_true]; exact hin w h
    · simp only [h, if_false]; rw [hout w h]; exact hT.1 w
  · filter_upwards [hT.2, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hwT
    rw [hout w hwT, hw]

theorem hasLev_zero : HasLev (0 : H E a b → ℂ) :=
  ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun _ _ _ => rfl⟩

theorem hasLev_add {G G' : H E a b → ℂ} (h : HasLev G) (h' : HasLev G') : HasLev (G + G') := by
  obtain ⟨U, hU, hG⟩ := h
  obtain ⟨U', hU', hG'⟩ := h'
  refine ⟨U ⊓ U', by rw [Subgroup.coe_inf]; exact hU.inter hU', fun u hu x => ?_⟩
  have hu' := Subgroup.mem_inf.1 hu
  simp only [Pi.add_apply, hG u hu'.1 x, hG' u hu'.2 x]

theorem hasLev_sum {ι : Type} (s : Finset ι) (g : ι → H E a b → ℂ) (h : ∀ i ∈ s, HasLev (g i)) :
    HasLev (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (hasLev_zero (E := E) (a := a) (b := b))
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact hasLev_add (h x (Finset.mem_insert_self x s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem uniform_lev {ι : Type} [Finite ι] (G : ι → H E a b → ℂ) (h : ∀ i, HasLev (G i)) :
    ∃ U : Subgroup (Hf E a b), IsOpen (U : Set (Hf E a b)) ∧ ∀ i, ∀ u ∈ U, ∀ x, G i (x * finH u) = G i x := by
  choose U hU hG using h
  refine ⟨⨅ i, U i, ?_, fun i u hu x => hG i u (Subgroup.mem_iInf.1 hu i) x⟩
  rw [Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite hU

theorem convF_congr {A A' κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (G : A × κ → H E a b → ℂ) (G' : A' × κ → H E a b → ℂ) (p : A) (q : A')
    (h : ∀ z, G (p, z) = G' (q, z)) (x : κ) : convF ν ψ G (p, x) = convF ν ψ G' (q, x) := by
  funext y
  simp only [convF, h]

theorem convF_zero {A κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) : convF ν ψ (0 : A × κ → H E a b → ℂ) = 0 := by
  funext i y
  simp [convF]

theorem iter_restrict {A κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (F : A × κ → H E a b → ℂ) (p : A) (k : ℕ) (x : κ) :
    (convF ν ψ)^[k] F (p, x) = (convF ν ψ)^[k] (fun i : Unit × κ => F (p, i.2)) ((), x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact convF_congr ν ψ _ _ p () (fun z => ih z) x

section
variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

def pw (M : LM κ a b) : ℕ → LM κ a b
  | 0 => M
  | k + 1 => M.mul (pw M k)

theorem mul_m (M M' : LM κ a b) (w : Pl E) (x y : κ w) :
    (M.mul M').m w x y = ∑ z, mconv (M.m w x z) (M'.m w z y) := rfl

theorem mul_s (M M' : LM κ a b) (w : Pl E) : (M.mul M').s w = mconv (M.s w) (M'.s w) := rfl

theorem product_torus_component (M M' : LM κ a b) (w : Pl E) : (M.mul M').t w = mconv (M.t w) (M'.t w) := rfl

def dg (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E) (x y : κ w) : GLw a w × GLw b w → ℂ :=
  if x = y then idem (V w) else fun _ => 0

def only0 (L : LM κ a b) (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w₀ : Pl E) : LM κ a b :=
  ⟨fun w x y => if w = w₀ then L.m w x y else dg V w x y, L.s, L.t⟩

def rest1 (L : LM κ a b) (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w₀ : Pl E) : LM κ a b :=
  ⟨fun w x y => if w = w₀ then dg V w x y else L.m w x y, L.s, L.t⟩

theorem dg_mul_left (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E) (x : κ w)
    (f : κ w → GLw a w × GLw b w → ℂ) : ∑ z, mconv (dg V w x z) (f z) = mconv (idem (V w)) (f x) := by
  rw [Finset.sum_eq_single x]
  · simp [dg]
  · intro z _ hz
    simp only [dg, if_neg (Ne.symm hz)]
    exact mconv_zero_left _
  · simp

theorem dg_mul_right (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E) (y : κ w)
    (f : κ w → GLw a w × GLw b w → ℂ) : ∑ z, mconv (f z) (dg V w z y) = mconv (f y) (idem (V w)) := by
  rw [Finset.sum_eq_single y]
  · simp [dg]
  · intro z _ hz
    simp only [dg, if_neg hz]
    exact mconv_zero_right _
  · simp

theorem mconv_idem_dg {V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)} {w : Pl E}
    (hV : IsOpen (V w : Set (GLw a w × GLw b w))) (hle : V w ≤ K2 a b w) (x y : κ w) :
    mconv (idem (V w)) (dg V w x y) = dg V w x y := by
  unfold dg
  split_ifs
  · exact mconv_idem_left hV hle fun v hv g => idem_left hv g
  · exact mconv_zero_right _

theorem stabilizerDilationWeights_dualIsotropicVector (M : LM κ a b) (W : ∀ w : Pl E, Subgroup (GLw a w × GLw b w))
    (hW : ∀ w, IsOpen (W w : Set (GLw a w × GLw b w)) ∧ W w ≤ K2 a b w) (hs : ∀ w, M.s w = idem (W w)) :
    ∀ k w, (pw M k).s w = idem (W w) := by
  intro k
  induction k with
  | zero => exact hs
  | succ k ih =>
    intro w
    show mconv (M.s w) ((pw M k).s w) = _
    rw [hs, ih]
    exact mconv_idem_left (hW w).1 (hW w).2 fun v hv g => idem_left hv g

theorem power_torus_component_idempotent (M : LM κ a b) (W : ∀ w : Pl E, Subgroup (GLw a w × GLw b w))
    (hW : ∀ w, IsOpen (W w : Set (GLw a w × GLw b w)) ∧ W w ≤ K2 a b w) (ht : ∀ w, M.t w = idem (W w)) :
    ∀ k w, (pw M k).t w = idem (W w) := by
  intro k
  induction k with
  | zero => exact ht
  | succ k ih =>
    intro w
    show mconv (M.t w) ((pw M k).t w) = _
    rw [ht, ih]
    exact mconv_idem_left (hW w).1 (hW w).2 fun v hv g => idem_left hv g

theorem pw_m_congr (M M' : LM κ a b) (w : Pl E) (h : M.m w = M'.m w) : ∀ k, (pw M k).m w = (pw M' k).m w := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    show (fun x y => ∑ z, mconv (M.m w x z) ((pw M k).m w z y)) =
      fun x y => ∑ z, mconv (M'.m w x z) ((pw M' k).m w z y)
    rw [h, ih]

theorem pw_dg (M : LM κ a b) (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E)
    (hV : IsOpen (V w : Set (GLw a w × GLw b w))) (hle : V w ≤ K2 a b w) (h : M.m w = dg V w) :
    ∀ k, (pw M k).m w = dg V w := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    funext x y
    show ∑ z, mconv (M.m w x z) ((pw M k).m w z y) = _
    rw [h, ih, dg_mul_left V w x (fun z => dg V w z y)]
    exact mconv_idem_dg hV hle x y

theorem pw_left (M : LM κ a b) (w : Pl E) (W : Subgroup (GLw a w × GLw b w))
    (h : ∀ x y, ∀ v ∈ W, ∀ g, M.m w x y (v * g) = M.m w x y g) :
    ∀ k x y, ∀ v ∈ W, ∀ g, (pw M k).m w x y (v * g) = (pw M k).m w x y g := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro x y v hv g
    show (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) (v * g) = (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) g
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun z _ => mconv_left (fun g' => h x z v hv g') g

theorem pw_right (M : LM κ a b) (w : Pl E) (W : Subgroup (GLw a w × GLw b w))
    (h : ∀ x y, ∀ v ∈ W, ∀ g, M.m w x y (g * v) = M.m w x y g) :
    ∀ k x y, ∀ v ∈ W, ∀ g, (pw M k).m w x y (g * v) = (pw M k).m w x y g := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro x y v hv g
    show (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) (g * v) = (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) g
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun z _ => mconv_right (fun g' => ih z y v hv g') g

end

section
variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

theorem pw_ok (hA : FmAlg) (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w)
    (hS : IsSection S) (hP : (↑P : Set (Pl E)) ⊆ S) (M : LM κ B.a B.b) (hM : M.Ok P) : ∀ k, (pw M k).Ok P := by
  intro k
  induction k with
  | zero => exact hM
  | succ k ih => exact (hA E κ S P B e hS hP M (pw M k) hM ih).2.1

theorem iter_pw (hA : FmAlg) (hC : ConvMul) (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E)
    (e : B.κ ≃ ∀ w : P, κ w) (hS : IsSection S) (hP : (↑P : Set (Pl E)) ⊆ S) (M : LM κ B.a B.b) (hM : M.Ok P)
    {A : Type} (G : A × B.κ → H E B.a B.b → ℂ) (U : Subgroup (Hf E B.a B.b)) (hU : IsOpen (U : Set (Hf E B.a B.b)))
    (hG : ∀ i, ∀ u ∈ U, ∀ x, G i (x * finH u) = G i x) :
    ∀ k, (convF B.ν (fm S P B e M))^[k + 1] G = convF B.ν (fm S P B e (pw M k)) G := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hk := pw_ok hA S P B e hS hP M hM k
    obtain ⟨h1, -, h3, -⟩ := hA E κ S P B e hS hP M (pw M k) hM hk
    have h2 := (hA E κ S P B e hS hP (pw M k) M hk hM).1
    rw [← (hC E B A _ _ U G h1 h2 hU hG).1, h3]
    rfl

end

end PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

attribute [local instance] borelG borelF borelH

open MatrixConvolutionPowers

theorem fmPowOf_holds : FmPowOf := by
  intro hA hAtP hC hAct hIdem
  intro E _ _ _ κ _ S P B e hS hP U₁ U₂ L A F m hU₁ hU₂ hL hs ht hbi hF hne w₀
  by_contra hcon
  push Not at hcon
  apply hne
  funext i
  obtain ⟨p, k⟩ := i

  choose V₁ V₂ hV₁ hV₂ hVU using fun w => exists_level_prod w (U₁ w) (hU₁.1 w).1 (hU₁.1 w).2
  set V : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w) := fun w => (V₁ w).prod (V₂ w) with hVdef
  have hVo : ∀ w, IsOpen (V w : Set (GLw B.a w × GLw B.b w)) := fun w => by
    rw [hVdef, Subgroup.coe_prod]; exact (hV₁ w).1.prod (hV₂ w).1
  have hVK : ∀ w, V w ≤ K2 B.a B.b w := fun w => Subgroup.prod_mono (hV₁ w).2.1 (hV₂ w).2.1
  have hVH : ∀ w, IsHecke (V w) (idem (V w)) := fun w => isHecke_idem (V₁ w) (V₂ w) (hV₁ w) (hV₂ w)
  have hdgH : ∀ w (x y : κ w), IsHecke (V w) (dg V w x y) := fun w x y => by
    unfold dg; split_ifs
    · exact hVH w
    · exact isHecke_zero _
  have hw₀P : w₀.1 ∈ P := w₀.2
  set L0 := only0 L V w₀.1 with hL0
  set L1 := rest1 L V w₀.1 with hL1
  have hL0s : L0.s = L.s := by rw [hL0]; rfl
  have hL0t : L0.t = L.t := by rw [hL0]; rfl
  have hL1s : L1.s = L.s := by rw [hL1]; rfl
  have hL1t : L1.t = L.t := by rw [hL1]; rfl
  clear_value L0 L1

  have hL0ok : L0.Ok P := by
    refine ⟨fun x y => isTestFunction_modify (hL.1 x y) (P.erase w₀.1) V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_), by rw [hL0t]; exact hL.2⟩
    · unfold LM.ent
      split_ifs with hwP
      · have : w = w₀.1 := by
          by_contra hne'; exact hw (Finset.mem_erase.2 ⟨hne', hwP⟩)
        subst this
        simp [hL0, only0]
      · rw [hL0s]
    · obtain ⟨hne', hwP⟩ := Finset.mem_erase.1 hw
      unfold LM.ent
      rw [dif_pos hwP]
      simp only [hL0, only0, if_neg hne']
      exact hdgH w _ _
  have hL1ok : L1.Ok P := by
    refine ⟨fun x y => isTestFunction_modify (hL.1 x y) {w₀.1} V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_), by rw [hL1t]; exact hL.2⟩
    · have hne' : w ≠ w₀.1 := fun h => hw (Finset.mem_singleton.2 h)
      unfold LM.ent
      split_ifs with hwP
      · simp [hL1, rest1, hne']
      · rw [hL1s]
    · rw [Finset.mem_singleton.1 hw]
      unfold LM.ent
      rw [dif_pos hw₀P]
      simp only [hL1, rest1, if_true]
      exact hdgH _ _ _

  set Φ : ∀ w : Pl E, GLw B.a w × GLw B.b w → ℂ := fun w => if w ∈ P then idem (V w) else L.s w with hΦ
  have hΦt : IsTestP Φ := by
    refine isTestFunction_modify (hL.1 (e k) (e k)) P V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_)
    · simp only [hΦ, if_neg hw, LM.ent, dif_neg hw]
    · simp only [hΦ, if_pos hw]; exact hVH w
  have hΨt : IsTestP L.t := hL.2
  let Good : (Unit × B.κ → H E B.a B.b → ℂ) → Prop := fun G =>
    ∀ i, HasLev (G i) ∧ ∀ j : Slot S, actS Φ L.t j (G i) = G i
  set i₀ : Slot S := Sum.inl ⟨w₀.1, hP w₀.2⟩ with hi₀

  have hform : ∀ G, Good G → ∀ x, convF B.ν (fm S P B e L0) G ((), x) =
      ∑ y : κ w₀, actP w₀.1 (L.m w₀.1 (e x w₀) y) (G ((), e.symm (Function.update (e x) w₀ y))) := by
    intro G hG x
    have hQ : Quiet S P B e L0 i₀ G := by
      refine ⟨fun w hwP hw x' y' hxy => ?_, fun j hj q x' y' hag => ?_⟩
      · have hne' : w ≠ w₀.1 := fun h => hw (hP hwP) (by subst h; rfl)
        simp only [hL0, only0, if_neg hne', dg, if_neg hxy]
        rfl
      · obtain ⟨⟩ := q
        cases j with
        | inl w' =>
          have hent : LM.ent P L0 (e x') (e y') w'.1 = Φ w'.1 := by
            unfold LM.ent
            by_cases hwP : w'.1 ∈ P
            · rw [dif_pos hwP]
              have hne' : w'.1 ≠ w₀.1 := fun h => hj (by rw [hi₀]; congr 1; exact Subtype.ext h)
              have hxy : e x' ⟨w'.1, hwP⟩ = e y' ⟨w'.1, hwP⟩ := hag ⟨w'.1, hwP⟩ fun h he =>
                hne' (congrArg Subtype.val (Sum.inl_injective he)).symm
              simp only [hL0, only0, if_neg hne', dg, hxy, if_true, hΦ, if_pos hwP]
            · rw [dif_neg hwP]
              simp only [hL0, only0, hΦ, if_neg hwP]
          show actP w'.1 (LM.ent P L0 (e x') (e y') w'.1) (G ((), y')) = G ((), y')
          rw [hent]
          exact (hG ((), y')).2 (Sum.inl w')
        | inr w' =>
          show actT w'.1 (L0.t w'.1) (G ((), y')) = G ((), y')
          rw [hL0t]
          exact (hG ((), y')).2 (Sum.inr w')
    have h := hAtP E κ S P B e hS hP Unit L0 w₀ G hL0ok (fun i => (hG i).1) hQ () x
    rw [h]
    simp only [hL0, only0, if_true]

  have hterm : ∀ (x : B.κ) (y : κ w₀) (g : H E B.a B.b → ℂ), HasLev g → (∀ j : Slot S, actS Φ L.t j g = g) →
      HasLev (actP w₀.1 (L.m w₀.1 (e x w₀) y) g) ∧
        ∀ j : Slot S, actS Φ L.t j (actP w₀.1 (L.m w₀.1 (e x w₀) y) g) = actP w₀.1 (L.m w₀.1 (e x w₀) y) g := by
    intro x y g hg hfix
    set ψ₁ := LM.ent P L (e x) (Function.update (e x) w₀ y) with hψ₁
    have hψt : IsTestP ψ₁ := hL.1 _ _
    have hψw : ψ₁ w₀.1 = L.m w₀.1 (e x w₀) y := by
      simp only [hψ₁, LM.ent, dif_pos hw₀P, Function.update_self]
    have hT : actP w₀.1 (L.m w₀.1 (e x w₀) y) g = actS ψ₁ L.t i₀ g := by
      show _ = actP w₀.1 (ψ₁ w₀.1) g
      rw [hψw]
    rw [hT]
    refine ⟨(hAct E B.a B.b S hS ψ₁ L.t ψ₁ L.t hψt hΨt hψt hΨt g g hg hg i₀ i₀).1, fun j => ?_⟩
    by_cases hj : j = i₀
    · subst hj
      have key := (hAct E B.a B.b S hS Φ L.t ψ₁ L.t hΦt hΨt hψt hΨt g g hg hg i₀ i₀).2.2.2
      rw [← key]
      show actP w₀.1 (mconv (Φ w₀.1) (ψ₁ w₀.1)) g = actP w₀.1 (ψ₁ w₀.1) g
      have hΦw : Φ w₀.1 = idem (V w₀.1) := by simp only [hΦ, if_pos hw₀P]
      rw [hΦw, mconv_idem_left (hVo _) (hVK _) fun v hv g' => ?_]
      rw [hψw]
      exact ((hbi w₀.1 hw₀P (e x w₀) y v (hVU w₀.1 hv) g').1)
    · rw [(hAct E B.a B.b S hS Φ L.t ψ₁ L.t hΦt hΨt hψt hΨt g g hg hg j i₀).2.2.1 hj, hfix j]

  have hact_sum : ∀ (j : Slot S) (s : Finset (κ w₀)) (T : κ w₀ → H E B.a B.b → ℂ), (∀ y, HasLev (T y)) →
      actS Φ L.t j (∑ y ∈ s, T y) = ∑ y ∈ s, actS Φ L.t j (T y) := by
    intro j s T hT
    induction s using Finset.induction_on with
    | empty =>
      have h0 := (hAct E B.a B.b S hS Φ L.t Φ L.t hΦt hΨt hΦt hΨt 0 0 hasLev_zero hasLev_zero j j).2.1 1
      simp only [add_zero, one_smul] at h0
      simpa using h0
    | insert z s hz ih =>
      rw [Finset.sum_insert hz, Finset.sum_insert hz]
      have h1 := (hAct E B.a B.b S hS Φ L.t Φ L.t hΦt hΨt hΦt hΨt (T z) (∑ y ∈ s, T y) (hT z)
        (hasLev_sum s T fun y _ => hT y) j j).2.1 1
      simp only [one_smul] at h1
      rw [h1, ih]

  have hgood : ∀ G, Good G → Good (convF B.ν (fm S P B e L0) G) := by
    intro G hG i
    obtain ⟨⟨⟩, x⟩ := i
    rw [hform G hG x]
    have hts := fun y => hterm x y _ (hG ((), e.symm (Function.update (e x) w₀ y))).1
      (hG ((), e.symm (Function.update (e x) w₀ y))).2
    refine ⟨hasLev_sum _ _ fun y _ => (hts y).1, fun j => ?_⟩
    rw [hact_sum j _ _ fun y => (hts y).1]
    exact Finset.sum_congr rfl fun y _ => (hts y).2 j
  have hgoodn : ∀ G, Good G → ∀ n, Good ((convF B.ν (fm S P B e L0))^[n] G) := by
    intro G hG n
    induction n with
    | zero => exact hG
    | succ n ih => rw [Function.iterate_succ_apply']; exact hgood _ ih

  have hslice : ∀ G, Good G → ∀ n (x' : ∀ w : P, κ w) (y : κ w₀),
      (convF B.ν (fm S P B e L0))^[n] G ((), e.symm (Function.update x' w₀ y)) =
        (locM w₀.1 (L.m w₀.1))^[n] (fun y => G ((), e.symm (Function.update x' w₀ y))) y := by
    intro G hG n
    induction n with
    | zero => intro x' y; rfl
    | succ n ih =>
      intro x' y
      rw [Function.iterate_succ_apply', hform _ (hgoodn G hG n), Function.iterate_succ_apply']
      simp only [Equiv.apply_symm_apply, Function.update_self, Function.update_idem, ih]
      rfl

  set Fp : Unit × B.κ → H E B.a B.b → ℂ := fun i => F (p, i.2) with hFp
  have hFgood : Good Fp := by
    intro i
    refine ⟨(hF (p, i.2)).1, fun j => ?_⟩
    cases j with
    | inl w' =>
      show actP w'.1 (Φ w'.1) (F (p, i.2)) = F (p, i.2)
      have hfix := ((hF (p, i.2)).2 w'.1 w'.2).1
      by_cases hwP : w'.1 ∈ P
      · simp only [hΦ, if_pos hwP]
        exact ((hIdem E B.a B.b w'.1 (V w'.1) (F (p, i.2)) (hVo _) (hVK _) (hF (p, i.2)).1).1).2
          (fixed_mono _ (hVU w'.1) hfix)
      · simp only [hΦ, if_neg hwP, hs]
        exact ((hIdem E B.a B.b w'.1 (U₁ w'.1) (F (p, i.2)) (hU₁.1 _).1 (hU₁.1 _).2 (hF (p, i.2)).1).1).2 hfix
    | inr w' =>
      show actT w'.1 (L.t w'.1) (F (p, i.2)) = F (p, i.2)
      rw [ht]
      exact ((hIdem E B.a B.b w'.1 (U₂ w'.1) (F (p, i.2)) (hU₂.1 _).1 (hU₂.1 _).2 (hF (p, i.2)).1).2).2
        (((hF (p, i.2)).2 w'.1 w'.2.1).2 w'.2.2)
  have hz : (convF B.ν (fm S P B e L0))^[m] Fp = 0 := by
    funext i
    obtain ⟨⟨⟩, k'⟩ := i
    have hk' : k' = e.symm (Function.update (e k') w₀ (e k' w₀)) := by simp
    rw [hk', hslice Fp hFgood m (e k') (e k' w₀)]
    have := congrFun (hcon p (e k')) (e k' w₀)
    simpa [hFp] using this
  rw [iter_restrict]
  show (convF B.ν (fm S P B e L))^[m] Fp ((), k) = 0
  obtain ⟨U, hU, hUF⟩ := uniform_lev Fp fun i => (hFgood i).1
  cases m with
  | zero => simpa using congrFun hz ((), k)
  | succ n =>

    have hok1 := pw_ok hA S P B e hS hP L1 hL1ok n
    have hok0 := pw_ok hA S P B e hS hP L0 hL0ok n
    have hWs : ∀ w, IsOpen (U₁ w : Set (GLw B.a w × GLw B.b w)) ∧ U₁ w ≤ K2 B.a B.b w := hU₁.1
    have hWt : ∀ w, IsOpen (U₂ w : Set (GLw B.a w × GLw B.b w)) ∧ U₂ w ≤ K2 B.a B.b w := hU₂.1
    have hent : ∀ x y, LM.ent P (pw L n) x y = LM.ent P ((pw L1 n).mul (pw L0 n)) x y := by
      intro x y
      funext w
      unfold LM.ent
      split_ifs with hwP
      · by_cases hw0 : w = w₀.1
        · subst hw0
          have e1 : (pw L1 n).m w₀.1 = dg V w₀.1 :=
            pw_dg L1 V w₀.1 (hVo _) (hVK _) (by funext x' y'; simp [hL1, rest1]) n
          have e0 : (pw L0 n).m w₀.1 = (pw L n).m w₀.1 :=
            pw_m_congr L0 L w₀.1 (by funext x' y'; simp [hL0, only0]) n
          rw [mul_m]
          rw [e1, e0, dg_mul_left V w₀.1 _ (fun z => (pw L n).m w₀.1 z (y ⟨w₀.1, hwP⟩))]
          refine (mconv_idem_left (hVo _) (hVK _) fun v hv g => ?_).symm
          exact pw_left L w₀.1 (V w₀.1) (fun x' y' v' hv' g' => (hbi w₀.1 hwP x' y' v' (hVU w₀.1 hv') g').1) n _ _ v hv g
        · have e1 : (pw L1 n).m w = (pw L n).m w :=
            pw_m_congr L1 L w (by funext x' y'; simp [hL1, rest1, hw0]) n
          have e0 : (pw L0 n).m w = dg V w :=
            pw_dg L0 V w (hVo _) (hVK _) (by funext x' y'; simp [hL0, only0, hw0]) n
          rw [mul_m]
          rw [e1, e0, dg_mul_right V w _ (fun z => (pw L n).m w (x ⟨w, hwP⟩) z)]
          refine (mconv_idem_right (hVo _) (hVK _) fun v hv g => ?_).symm
          exact pw_right L w (V w) (fun x' y' v' hv' g' => (hbi w hwP x' y' v' (hVU w hv') g').2) n _ _ v hv g
      · rw [mul_s]
        rw [stabilizerDilationWeights_dualIsotropicVector L U₁ hWs hs n, stabilizerDilationWeights_dualIsotropicVector L1 U₁ hWs (by rw [hL1s]; exact hs) n, stabilizerDilationWeights_dualIsotropicVector L0 U₁ hWs (by rw [hL0s]; exact hs) n]
        exact (mconv_idem_left (hWs w).1 (hWs w).2 fun v hv g => idem_left hv g).symm
    have htt : (pw L n).t = ((pw L1 n).mul (pw L0 n)).t := by
      funext w
      rw [product_torus_component]
      rw [power_torus_component_idempotent L U₂ hWt ht n, power_torus_component_idempotent L1 U₂ hWt (by rw [hL1t]; exact ht) n, power_torus_component_idempotent L0 U₂ hWt (by rw [hL0t]; exact ht) n]
      exact (mconv_idem_left (hWt w).1 (hWt w).2 fun v hv g => idem_left hv g).symm
    have hfm : fm S P B e (pw L n) = fm S P B e ((pw L1 n).mul (pw L0 n)) := by
      funext x y h
      simp only [fm, hent, htt]
    obtain ⟨hf1, -, hmul, -⟩ := hA E κ S P B e hS hP (pw L1 n) (pw L0 n) hok1 hok0
    have hf0 := (hA E κ S P B e hS hP (pw L0 n) (pw L1 n) hok0 hok1).1
    rw [iter_pw hA hC S P B e hS hP L hL Fp U hU hUF n, hfm, ← hmul, (hC E B Unit _ _ U Fp hf1 hf0 hU hUF).1,
      ← iter_pw hA hC S P B e hS hP L0 hL0ok Fp U hU hUF n, hz, convF_zero]
    rfl

end PositivityTheory.Rg.BcB.F.FA

end
end

section
namespace PositivityTheory.Rg.BcB.F.FA

theorem position_action_algebra : ActAlg := GlobalTheory.CompanionTheory.FactorAction.actAlg

theorem finAct_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) : FinAct := GlobalTheory.CompanionTheory.FinActS.finActOf h1 h2 h3 position_action_algebra

theorem fmOne_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) : Tail.FmOne :=
  fmOneOf_holds (fmOff_holds h3 (finAct_of h1 h2 h3)) actIdem_holds

theorem fmPow_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) (h4 : FmAlg) : Tail.FmPow :=
  fmPowOf_holds h4 (fmAtP_holds h3 (finAct_of h1 h2 h3)) convMul_holds position_action_algebra actIdem_holds

end PositivityTheory.Rg.BcB.F.FA
end
