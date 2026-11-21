import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumFoldrLocalCombinations
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumFactorsOverTwistPrimesLocal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistParahoricChainLastStepsAgreeColumns
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleCharacterAtBasePointDetRootRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffUpMemStdHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeEntriesMemSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistQuadraticLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalIdentityStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleCharacter_at_basePointDetRoot_rootOfUnity : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ j, j < B.R.m → ∀ i, i ≤ B.R.m → ∀ β, ∃ n : ℕ, 0 < n ∧ A.chr (j + 1) (A.xr i β) ^ n = 1 := by
  first | exact @GlobalTheory.CharRoot.chr_xr_pow_eq_one | exact GlobalTheory.CharRoot.chr_xr_pow_eq_one | (intros; apply GlobalTheory.CharRoot.chr_xr_pow_eq_one <;> assumption)
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LevelLaw

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : Type} [Fintype n] [DecidableEq n]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n : Type} [Fintype n] [DecidableEq n] in
private theorem reGL_mem_KO_of_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) {g : GL a k} (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k a) :
    _root_.GlobalTheory.StepData.reGL e g ∈ _root_.GlobalTheory.SplitWeil.KO k b := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv, _root_.GlobalTheory.StepData.reGL_val, _root_.GlobalTheory.StepData.reGL_val]
  obtain ⟨h1, h2⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff _).mp hg
  exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

open MeasureTheory ValuativeRel Matrix in
private theorem exists_pos_pow_eq_one_of_isTame_of_valuation_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {δ : kˣ →* ℂˣ} (hδ : _root_.GlobalTheory.SplitWeil.IsTame δ) {u : kˣ} (hu : valuation k (u : k) = 1) : ∃ n : ℕ, 0 < n ∧ δ u ^ n = 1 := by
  classical
  have hO := Valuation.integer.integers (valuation k)
  let x : 𝒪[k] := ⟨u, by rw [Valuation.mem_integer_iff, hu]⟩
  have hx : IsUnit x := hO.isUnit_iff_valuation_eq_one.mpr hu
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  have hr : IsLocalRing.residue 𝒪[k] x ≠ 0 := (RingHom.isUnit_map _ hx).ne_zero
  have hq : 1 < Fintype.card (IsLocalRing.ResidueField 𝒪[k]) := Fintype.one_lt_card
  refine ⟨Fintype.card (IsLocalRing.ResidueField 𝒪[k]) - 1, by omega, ?_⟩
  have hmem : x ^ (Fintype.card (IsLocalRing.ResidueField 𝒪[k]) - 1) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  have hnu := mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
  have hlt := lt_of_le_of_ne (hO.map_le_one _) (mt hO.isUnit_iff_valuation_eq_one.mpr hnu)
  rw [← map_pow]
  apply hδ
  refine lt_of_eq_of_lt ?_ hlt
  simp [x]
  rfl

open MeasureTheory ValuativeRel Matrix in
private theorem hasTypes_apply_mul_left_of_mem_J_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {μ : kˣ →* ℂˣ} {P : _root_.GlobalTheory.StepData.Level (GL a k)} {Q : _root_.GlobalTheory.StepData.Level (GL b k)} {Φ : Matrix b a k → ℂ} (hΦ : _root_.GlobalTheory.StepData.HasTypes μ P Q Φ) {g : GL b k} (hg : g ∈ Q.J) (hgi : g ∈ _root_.GlobalTheory.SplitWeil.KO k b) (B : Matrix b a k) :
    Φ (g.val * B) = ((Q.lam ⟨g, hg⟩ : ℂ) * ((μ (GeneralLinearGroup.det g) : ℂ))⁻¹) * Φ B := by
  have key := congrFun (hΦ.2 ⟨g⁻¹, inv_mem hg⟩) B
  have hn : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g⁻¹) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO (inv_mem hgi))
  have hl : Q.lam ⟨g⁻¹, inv_mem hg⟩ = (Q.lam ⟨g, hg⟩)⁻¹ := map_inv Q.lam ⟨g, hg⟩
  rw [map_inv] at hn
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, Units.smul_def, inv_inv, Matrix.mul_one, hl, hn, map_one, Real.one_rpow, Units.val_one, one_mul, map_inv, Units.val_inv_eq_inv_val, Complex.ofReal_one, mul_one, Units.val_one, _root_.GlobalTheory.SplitWeil.nabs_one, smul_eq_mul] at key
  rw [mul_right_comm, ← key, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

open MeasureTheory ValuativeRel Matrix in
private theorem hasTypes_apply_mul_right_of_mem_J_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {μ : kˣ →* ℂˣ} {P : _root_.GlobalTheory.StepData.Level (GL a k)} {Q : _root_.GlobalTheory.StepData.Level (GL b k)} {Φ : Matrix b a k → ℂ} (hΦ : _root_.GlobalTheory.StepData.HasTypes μ P Q Φ) {g : GL a k} (hg : g ∈ P.J) (hgi : g ∈ _root_.GlobalTheory.SplitWeil.KO k a) (B : Matrix b a k) :
    Φ (B * g.val) = ((P.lam ⟨g, hg⟩ : ℂ) * ((μ (GeneralLinearGroup.det g) : ℂ))⁻¹) * Φ B := by
  have key := congrFun (hΦ.1 ⟨g, hg⟩) B
  have hn : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hgi)
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, Units.smul_def, inv_one, Matrix.one_mul, hn, map_one, Real.one_rpow, Units.val_one, one_mul, inv_one, Complex.ofReal_one, mul_one, _root_.GlobalTheory.SplitWeil.nabs_one, smul_eq_mul] at key
  rw [mul_right_comm, ← key, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

open MeasureTheory ValuativeRel Matrix in
private theorem withCol_toBlocks11_mul_mulVec_eq_mul_withCol {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] (g : GL (n ⊕ Fin 0) k) (x : Matrix n n' k) (y : n → k) : _root_.GlobalTheory.StepData.withCol (g.val.toBlocks₁₁ * x) (g.val.toBlocks₁₁ *ᵥ y) = g.val * _root_.GlobalTheory.StepData.withCol x y := by
  ext (i | i) (j | j)
  · simp [_root_.GlobalTheory.StepData.withCol, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁]
  · simp [_root_.GlobalTheory.StepData.withCol, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁, mulVec, dotProduct]
  · exact i.elim0
  · exact i.elim0

open MeasureTheory ValuativeRel Matrix in
private theorem fromCols_zero_mul_toBlocks11_eq_mul_val {k : Type} [Field k] {n m : Type} [Fintype n] [DecidableEq n] (g : GL (n ⊕ Fin 0) k) (x : Matrix (m ⊕ Unit) n k) :
    (x * g.val.toBlocks₁₁).toRows₁.fromCols 0 = x.toRows₁.fromCols 0 * g.val := by
  ext i (j | j)
  · change _ = ∑ l, (x.toRows₁.fromCols (0 : Matrix m (Fin 0) k)) i l * (g : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) l (Sum.inl j)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, toRows₁, toBlocks₁₁]
  · exact j.elim0

open MeasureTheory ValuativeRel Matrix in
private theorem mul_apply_inr_unit_eq_vecMul {k : Type} [Field k] {n m : Type} [Fintype n] (x : Matrix (m ⊕ Unit) n k) (B : Matrix n n k) :
    (x * B) (Sum.inr ()) = x (Sum.inr ()) ᵥ* B := by
  funext j
  simp [Matrix.mul_apply, vecMul, dotProduct]

open MeasureTheory ValuativeRel Matrix in
private theorem mulVec_mem_box_of_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] (G : GL n k) (hG : G ∈ _root_.GlobalTheory.SplitWeil.KO k n) (w : kˣ) {m : n → k} (hm : m ∈ _root_.GlobalTheory.StepData.box n w) : (G : Matrix n n k) *ᵥ m ∈ _root_.GlobalTheory.StepData.box n w := by
  rw [_root_.GlobalTheory.StepData.mem_box] at hm ⊢
  intro i
  have hGi := ((_root_.GlobalTheory.SplitFlip.mem_KO_iff G).mp hG).1 i
  refine (Valuation.map_sum_le _ fun j _ => ?_)
  rw [map_mul]
  calc valuation k ((G : Matrix n n k) i j) * valuation k (m j) ≤ 1 * valuation k (m j) := by
        gcongr
        exact (Valuation.mem_integer_iff _ _).mp (hGi j)
    _ ≤ valuation k (w : k) := by rw [one_mul]; exact hm j

open MeasureTheory ValuativeRel Matrix in
private theorem hat_cosetInd_box_vecMul_KO_eq_mulVec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (ε : k) (G : GL n k) (hG : G ∈ _root_.GlobalTheory.SplitWeil.KO k n) (w : kˣ) (y v : n → k) :
    _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk y)) (v ᵥ* (G : Matrix n n k)) =
      _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y))) v := by
  have hdet : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det G) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hG)
  have hiff : ∀ z : n → k, (Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n w) z = Submodule.Quotient.mk y) ↔
      (Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n w) ((G : Matrix n n k) *ᵥ z) = Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y)) := by
    intro z
    simp only [Submodule.Quotient.eq, ← mulVec_sub]
    refine ⟨mulVec_mem_box_of_mem_KO G hG w, fun h => ?_⟩
    have := mulVec_mem_box_of_mem_KO G⁻¹ (inv_mem hG) w h
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
  unfold _root_.GlobalTheory.StepData.hat
  have h := _root_.GlobalTheory.SplitWeil.integral_comp_mulVec_eq_smul ν G (fun z => _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y)) z * ((ψ (ε * v ⬝ᵥ z) : Circle) : ℂ))
  rw [hdet, inv_one, one_smul] at h
  rw [← h]
  congr 1
  ext z
  rw [dotProduct_mulVec]
  congr 1
  unfold _root_.GlobalTheory.StepData.cosetInd
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [← hiff z]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n : Type} [Fintype n] [DecidableEq n] in

theorem _root_.GlobalTheory.LevelLaw.last_steps_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), _root_.GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : _root_.GlobalTheory.SplitWeil.IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, _root_.GlobalTheory.SplitWeil.IsUnram (η j)) → ∀ g : GL (_root_.GlobalTheory.StepData.XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : _root_.GlobalTheory.StepData.XIx κ t (s + 1) → k) x, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).xiTop (_root_.GlobalTheory.StepData.box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).xiTop (_root_.GlobalTheory.StepData.box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  intro k _ _ _ _ _ _ ν hν s κ t _ _ _ _ δ hδ η hη g hg
  haveI := hν.1
  set F := _root_.GlobalTheory.StepData.plainFrame (k := k) (_root_.GlobalTheory.StepData.stdOrd κ t (l := s + 1) (s + 1) 0 rfl) with hF
  have hg' : F.conj.symm g ∈ (_root_.GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 1) × t) δ hδ).J :=
    _root_.GlobalTheory.StepData.Level.mem_map.mp hg
  have hgg : g = _root_.GlobalTheory.StepData.reGL F.ord (F.conj.symm g) := by
    have := F.conj_apply (F.conj.symm g)
    rw [MulEquiv.apply_symm_apply] at this
    simpa [hF, _root_.GlobalTheory.StepData.plainFrame] using this
  have hlam : ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).lam ⟨g, hg⟩ =
      (_root_.GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 1) × t) δ hδ).lam ⟨F.conj.symm g, hg'⟩ :=
    _root_.GlobalTheory.StepData.Level.map_lam _ _ _
  obtain ⟨hg'int, hg'low⟩ := _root_.GlobalTheory.StepData.mem_parahoric.mp hg'
  obtain ⟨⟨A, hA, hAeq⟩, ⟨D, -, hDeq⟩⟩ := _root_.GlobalTheory.StepData.exists_diag_blocks hg'int hg'low
  have hint : g ∈ _root_.GlobalTheory.SplitWeil.KO k _ := by
    rw [hgg]
    exact reGL_mem_KO_of_mem_KO _ hg'int
  have hdet : GeneralLinearGroup.det g = GeneralLinearGroup.det (F.conj.symm g) := by
    conv_lhs => rw [hgg]
    exact _root_.GlobalTheory.StepData.det_reGL _ _
  have hsplit := _root_.GlobalTheory.StepData.tame_det_blocks hδ hg'int hg'low hAeq hDeq
  have hval := _root_.GlobalTheory.StepData.valuation_det_of_mem_KO hint
  set c : ℂˣ := ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).lam ⟨g, hg⟩ *
    (δ (GeneralLinearGroup.det g))⁻¹ with hc
  have hcA : c = (δ (GeneralLinearGroup.det A))⁻¹ := by
    rw [hc, hlam, _root_.GlobalTheory.StepData.parahoric_lam _ D hDeq, hdet, hsplit, _root_.mul_inv_rev, mul_inv_cancel_left]
  have hroot : ∃ n : ℕ, 0 < n ∧ (c : ℂ) ^ n = 1 := by
    obtain ⟨n, hn, hpow⟩ := exists_pos_pow_eq_one_of_isTame_of_valuation_eq_one hδ (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hA)
    exact ⟨n, hn, by rw [← Units.val_pow_eq_pow_val, hcA, inv_pow, hpow, inv_one, Units.val_one]⟩
  have hL := _root_.GlobalTheory.StepData.Chain.ofTwist_laws δ hδ η hη
    (fun j c h ↦ _root_.GlobalTheory.StepData.plainFrame (_root_.GlobalTheory.StepData.stdOrd κ t j c h))
    (_root_.GlobalTheory.StepData.LatFrame.refl k (_root_.GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) t (s + 2)))
  have hmu : ∀ j, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu j (GeneralLinearGroup.det g) =
      δ (GeneralLinearGroup.det g) := by
    intro j
    change (η j * δ) (GeneralLinearGroup.det g) = _
    rw [MonoidHom.mul_apply, hη j _ hval, one_mul]
  have hΦ := hasTypes_apply_mul_left_of_mem_J_KO (μ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu (s + 1))
    (Φ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl) (hL.1 s 0 rfl) hg hint
  have hTop := hasTypes_apply_mul_right_of_mem_J_KO (μ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu (s + 2))
    (Φ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop) hL.2 hg hint
  rw [hmu] at hΦ hTop
  have hΦ' : ∀ B, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl (g.val * B) =
      c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl B := by
    intro B
    rw [hΦ B, hc, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hTop' : ∀ B, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop (B * g.val) =
      c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop B := by
    intro B
    rw [hTop B, hc, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  obtain ⟨G, hGi, hGeq⟩ : ∃ G : GL (_root_.GlobalTheory.StepData.XIx κ t (s + 1)) k,
      G ∈ _root_.GlobalTheory.SplitWeil.KO k _ ∧ (G : Matrix _ _ k) = g.val.toBlocks₁₁ :=
    ⟨_root_.GlobalTheory.StepData.reGL (Equiv.sumEmpty _ (Fin 0)) g, reGL_mem_KO_of_mem_KO _ hint, by
      rw [_root_.GlobalTheory.StepData.reGL_val]
      rfl⟩
  refine ⟨c, hroot, ?_, ?_⟩
  · intro h x₀ y
    unfold _root_.GlobalTheory.StepData.Chain.Psi
    rw [withCol_toBlocks11_mul_mulVec_eq_mul_withCol]
    simp only [_root_.GlobalTheory.SplitWeil.om, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [hΦ']
    ring
  · intro ψ ε w y x
    unfold _root_.GlobalTheory.StepData.Chain.xiTop
    rw [fromCols_zero_mul_toBlocks11_eq_mul_val, mul_apply_inr_unit_eq_vecMul]
    erw [hTop']
    rw [← hGeq, hat_cosetInd_box_vecMul_KO_eq_mulVec ν ψ ε G hGi w y]
    ring

end GlobalTheory.LevelLaw
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricChain_last_two_steps_root_of_unity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → ∀ g : GL (XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : XIx κ t (s + 1) → k) x, (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  atlas_forward_decl GlobalTheory.LevelLaw.last_steps_law
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.TwPlaces

theorem rou_mul {x y : ℂ} (hx : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) (hy : ∃ n : ℕ, 0 < n ∧ y ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (x * y) ^ n = 1 := by
  obtain ⟨n, hn, hx⟩ := hx
  obtain ⟨m, hm, hy⟩ := hy
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [mul_pow, pow_mul, hx, one_pow, one_mul, mul_comm, pow_mul, hy, one_pow]

theorem rou_inv {x : ℂ} (hx : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) : ∃ n : ℕ, 0 < n ∧ x⁻¹ ^ n = 1 := by
  obtain ⟨n, hn, hx⟩ := hx
  exact ⟨n, hn, by rw [inv_pow, hx, inv_one]⟩

theorem rou_prod {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, ∃ n : ℕ, 0 < n ∧ f i ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (∏ i ∈ s, f i) ^ n = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact rou_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem rou_circle {x : Circle} (h : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) : ∃ n : ℕ, 0 < n ∧ (x : ℂ) ^ n = 1 := by
  obtain ⟨n, hn, hx⟩ := h
  exact ⟨n, hn, by rw [← Circle.coe_pow, hx, Circle.coe_one]⟩

theorem toLoc_frames {E k : Type} [Field E] [Field k] (ι : E →+* k) {A C : Type} [Fintype A] [Fintype C] {a b a' b' : ℕ}
    (ha : a' = a) (hb : b' = b) (e : C ≃ Fin b) (e' : A ≃ Fin a) (f' : (Fin a → E) ≃ₗ[E] (Fin a → E))
    (f : (Fin b → E) ≃ₗ[E] (Fin b → E)) (z : Matrix (Fin b') (Fin a') E) (M : Matrix (Fin b') C k) (M' : Matrix (Fin a') A k)
    (hM : ∀ r c, ι (f (Pi.single (e c) 1) (finCongr hb r)) = M r c)
    (hM' : ∀ r c, ι (f' (Pi.single (e' c) 1) (finCongr ha r)) = M' r c) :
    M * (GlobalTheory.SymBridge.toLoc ι e e' (Formalism.L2.Col.inFr f' f (Matrix.toLin' (z.reindex (finCongr hb) (finCongr ha)))) : Matrix C A k) =
      z.map ι * M' := by
  subst ha hb
  have key : ∀ (y : Fin b' → E) r, ∑ c, M r c * ι (f.symm y (e c)) = ι (y r) := by
    intro y r
    have h4 : y = ∑ c, f.symm y (e c) • f (Pi.single (e c) 1) := by
      conv_lhs => rw [← f.apply_symm_apply y, pi_eq_sum_univ' (f.symm y), map_sum, ← e.sum_comp]
      exact Finset.sum_congr rfl fun b _ => map_smul _ _ _
    conv_rhs => rw [h4, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hM r c, Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]
    rfl
  ext r c
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine (key (Matrix.toLin' (z.reindex (finCongr rfl) (finCongr rfl)) (f' (Pi.single (e' c) 1))) r).trans ?_
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, ← hM' q c]
  rfl

theorem frame_cancel {k : Type} [Field k] {N N' : ℕ} {Y Y' : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y)
    {T : Matrix Y Y' k} {z : Matrix (Fin N) (Fin N') k} {M : Matrix (Fin N') Y' k} (h : F.β * T = z * M) : T = F.γ * z * M := by
  rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, F.γβ, Matrix.one_mul]

theorem isLocFac_of {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (hU : q.UnitAA) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (hd : DenseRange (ofSplit q).pr) (ψ : AddChar (AF D.host.F) ℂ) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (eS : ∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) (eT : ∀ z, z ∈ LT ↔ z ∈ intVec D T.rank)
    (fS : ∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v))
    (fT : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v))
    (c : WO S T →₀ ℂ) (Ξk : Matrix Y Y' k → ℂ) (hSB : Ξk ∈ SB (Matrix Y Y' k)) (hc : (ofSplit q).IsCombAt ψ FS FT c Ξk)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (hΞ : ∀ z, Ξ z = Ξk (FT.γ * z.map (ofSplit q).pr * FS.β)) :
    GlobalTheory.LocMod.IsLocFac D ψ S T PP c Ξ ∧ GlobalTheory.FinPl.CombAt (· = q.v) c :=
  ⟨⟨k, inferInstance, inferInstance, inferInstance, inferInstance, ofSplit q, Y, Y', inferInstance, inferInstance, inferInstance,
    inferInstance, FS, FT, Ξk, hd, hq,
    GlobalTheory.StdHomAt.int_iff_up_mem_stdHom D k q hU Y Y' S T FS FT LS LT hS hT eS eT fS fT, hSB, hc, hΞ⟩,
    fun u hu r s => (GlobalTheory.FinPl.FrameLat.idem_iff q _).2 (hc.1 u hu r s)⟩

theorem xiTop_mem_SB {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z) (hT : T.Regular) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (w : kˣ)
    (yb : (X (s + 1) → k) ⧸ box (X (s + 1)) w) : T.xiTop (box _ w) ψ ν (-1) yb ∈ SB (Matrix (Z ⊕ Unit) (X (s + 1)) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z ⊕ Unit) (n' := X (s + 1))
  have hv1 : valuation k (-1 : k) = 1 := by simp
  have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol k ψ ν (-1) hψ hν hv1 (X (s + 1)) 1 1 _ (cosetInd_mem_SB w yb)).1
  refine GlobalTheory.FinPl.Comm.prod_mem_SB hT.2.1 hh
    (p := fun x : Matrix (Z ⊕ Unit) (X (s + 1)) k => fromCols x.toRows₁ (0 : Matrix Z (Fin 0) k))
    (r := fun x => x (Sum.inr ()))
    (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
      · exact j.elim0
  · exact continuous_apply _
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases i with i | i
      · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
      · exact (continuous_apply j).comp continuous_snd
  · intro x; ext (i | i) j <;> rfl

section Steps

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T} (J : QJ a t) (i : Fin J.r)

def sgnAt (j : ℕ) (hj : j < B.R.m) (β : J.Ch₀ j) (n : ℕ) : ℂ :=
  GlobalTheory.TwBridge.sgn I.sel (I.tup (W.P.I.tup t)) (J.P i) ((J.E i).tw (J.hψ i) (J.sg i))
    ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) n

def FacAt (j : ℕ) (hj : j + 1 ≤ B.R.m) (α : J.Ch j) (γ : J.Ch (j + 1)) (c : ℂ) : Prop :=
  GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (pk W).ψ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) (J.pl i) ((J.E i).dL j (α i) (γ i))
               (fun z => c * B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z))) ∧
    GlobalTheory.FinPl.CombAt (S := (I.rec7 l Z).sp.X j) (T := (I.rec7 l Z).sp.X (j + 1)) (· = (J.G i).q.v) ((J.E i).dL j (α i) (γ i))

variable {J i}

theorem facAt_mid (hW : AllTrue W) (ha : a.Is) (haT : a.True) (hJ : J.Reads)
    (hm : MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i)) (j d : ℕ) (H : j + 1 + d = (J.G i).s) (hj : j + 1 ≤ B.R.m)
    (hj' : j + 1 < B.R.m) (α : J.Ch j) (γ : J.Ch (j + 1)) :
    FacAt J i j hj α γ (sgnAt J i j hj (J.ι j α) (B.R.N (j + 1) + Formalism.L2.Col.cOf B.R (j + 1)) *
      sgnAt J i (j + 1) hj' (J.ι (j + 1) γ) (B.R.N j + Formalism.L2.Col.cOf B.R j)) := by
  have H' : j + 1 + d = (a.Q (J.pl i) ⟨t, J.mem i⟩).s := H
  refine isLocFac_of (J.G i).q (J.G i).unit (J.G i).idem (J.G i).compl.dense _ ((J.G i).FX j (by omega)) ((J.G i).FX (j + 1) (by omega))
    (a.g.x j).L (a.g.x (j + 1)).L (ha.x j (Nat.le_of_succ_le hj)).sd (ha.x (j + 1) hj).sd (haT.pinX.xs j (Nat.le_of_succ_le hj)).2.2
    (haT.pinX.xs (j + 1) hj).2.2 ((J.G i).latX j _) ((J.G i).latX (j + 1) _) _ _
    (GlobalTheory.StepData.xi_mem_SB _ _ _ _ _ (J.hψ i) _ (J.G i).unitVol.1 _ ⟨_, (J.E i).reg.1 j (d + 1) (by omega)⟩ _ _ _ _)
    ((J.E i).dL_mid j d H (α i) (γ i)) _ fun z => ?_
  obtain ⟨e', he'⟩ := exists_xOrd B.R j
  obtain ⟨e, he⟩ := exists_xOrd B.R (j + 1)
  have h1 := (GlobalTheory.T.finiteDatum_factors_over_twistPrimes_local I hW.tr.ok hW.tr.tw l Z u _ J.Ch₀ J.A hJ.is).2 _ rfl _ _ _ (J.G i) _ (J.E i) (J.hψ i) (J.sg i) (J.π i) (J.P i)
    hm.toReadsAt j d H hj hj' (J.ι j α) (J.ι (j + 1) γ) e' e he' he (homOf I l Z j hj z)
  rw [hJ.sec j (Nat.le_of_succ_le hj), hJ.sec (j + 1) hj] at h1
  have h2 := toLoc_frames ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj))
    (rankN (I.rec7 l Z) (j + 1) hj) e e' _ _ z _ _ (hm.low (j + 1) (by omega) hj (J.ι (j + 1) γ) e he)
    (hm.low j (by omega) (Nat.le_of_succ_le hj) (J.ι j α) e' he')
  exact h1.symm.trans (congrArg _ (frame_cancel ((J.G i).FX (j + 1) (by omega)) h2))

theorem lastAgree_at (hW : AllTrue W) (hJ : J.Reads) :
    GlobalTheory.TwBridge.LastAgree I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
      ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i)) (J.G i).ν (I.idx (W.P.I.tup t)) := by
  have hI := hW.tr.ok
  have hs : (J.G i).s = B.R.m - 2 := by have := (hJ.tw i).steps; omega
  have hL : (I.idx (W.P.I.tup t)).Ok I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) I.glob (J.G i).s := by
    rw [hs]; exact hI.idx_ok _
  exact GlobalTheory.T.twistParahoricChain_lastSteps_agree_columns B.fields (B.primes X) B.R I.Ch I.sel _ _ _ B.embLL (J.P i) (J.G i).k _ (J.G i).s _ (J.G i).ν (J.G i).unitVol
    (hI.idx_ok _).cst_ok (hJ.tw i) _ I.glob hL

variable (J i) in

def MoveAt (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))) (hm : (J.G i).s + 1 ≤ B.R.m)
    (β : J.Ch₀ ((J.G i).s + 1)) (c : ℂ) : Prop :=
  ∃ κ : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k,
    (∀ r b, (ofSplit (J.G i).q).pr (baseFr J.A (J.P i) ((J.G i).s + 1) hm β r (e b)) =
      (((J.G i).FX ((J.G i).s + 1) le_rfl).β * κ.val.toBlocks₁₁) r b) ∧
    (J.E i).cos (J.π i ((J.G i).s + 1) β) = Submodule.Quotient.mk (κ.val.toBlocks₁₁ *ᵥ ownVec J.A (J.G i) (J.P i) e β) ∧
    (∀ h x₀ y, ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).Psi h (κ.val.toBlocks₁₁ * x₀) (κ.val.toBlocks₁₁ *ᵥ y) =
      c * ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).Psi h x₀ y) ∧
    ∀ (ψ : AddChar (J.G i).k Circle) (ε : (J.G i).k) (w : (J.G i).kˣ) y x,
      ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).xiTop (box _ w) ψ (J.G i).ν ε (Submodule.Quotient.mk y) (x * κ.val.toBlocks₁₁) =
        c * ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).xiTop (box _ w) ψ (J.G i).ν ε (Submodule.Quotient.mk (κ.val.toBlocks₁₁ *ᵥ y)) x

theorem exists_moveAt (hm : MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i)) (e) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e)
    (h : (J.G i).s + 1 ≤ B.R.m) (β) : ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ MoveAt J i e h β c := by
  obtain ⟨κ, hκ, h1, h2⟩ := hm.pen h β e he
  obtain ⟨c, hc, h3, h4⟩ := GlobalTheory.T.parahoricChain_last_two_steps_root_of_unity (J.G i).k (J.G i).ν (J.G i).unitVol (J.G i).s (Fin B.R.k) (Fin B.R.t) (J.E i).δ (J.E i).tame
    (J.E i).η (J.E i).unr κ hκ
  exact ⟨c, hc, κ, h1, h2, h3, h4⟩

theorem facAt_pen (hW : AllTrue W) (ha : a.Is) (haT : a.True) (hJ : J.Reads)
    (hm : MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i)) (hj : (J.G i).s + 1 ≤ B.R.m) (e)
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e) (α : J.Ch (J.G i).s) (γ : J.Ch ((J.G i).s + 1)) (c : ℂ)
    (hc : MoveAt J i e hj (J.ι _ γ) c) :
    FacAt J i (J.G i).s hj α γ (sgnAt J i _ hj (J.ι _ α) (B.R.N ((J.G i).s + 1) + Formalism.L2.Col.cOf B.R ((J.G i).s + 1)) * c) := by
  refine isLocFac_of (J.G i).q (J.G i).unit (J.G i).idem (J.G i).compl.dense _ ((J.G i).FX _ (Nat.le_succ _)) ((J.G i).FX _ le_rfl)
    (a.g.x _).L (a.g.x _).L (ha.x _ (Nat.le_of_succ_le hj)).sd (ha.x _ hj).sd (haT.pinX.xs _ (Nat.le_of_succ_le hj)).2.2
    (haT.pinX.xs _ hj).2.2 ((J.G i).latX _ _) ((J.G i).latX _ _) _ _
    (GlobalTheory.QPl.LastTwo.entries_mem_SB _ _ _ _ (J.E i).toAt (α i) ((J.E i).cos (γ i))).1
    ((J.E i).dL_pen (α i) (γ i)) _ fun z => ?_
  obtain ⟨e', he'⟩ := exists_xOrd B.R (J.G i).s
  obtain ⟨κ, h1, h2, h3, -⟩ := hc
  have hs : (J.G i).s + 2 = B.R.m := (J.G i).hs
  have hA := ((lastAgree_at (i := i) hW hJ).1 ((J.A.b0 _ (J.ι _ α)).get hj) _ (hJ.rep i _ 0 rfl hj (J.ι _ α))).2 e' e he' he
    (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ α)).1.1 (J.P i))
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ γ)).1.1 (J.P i)) (homOf I l Z _ hj z))
    ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ γ)).1.1 (J.P i)).symm (Formalism.L2.Col.repY (J.A.p0 _ (J.ι _ γ)).1.2))
  rw [hJ.sec _ (Nat.le_of_succ_le hj)] at hA
  rw [hJ.sec _ hj] at h2
  have h4 := toLoc_frames ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (rankN (I.rec7 l Z) _ (Nat.le_of_succ_le hj))
    (rankN (I.rec7 l Z) _ hj) e e' _ _ z _ _ h1 (hm.low _ le_rfl (Nat.le_of_succ_le hj) (J.ι _ α) e' he')
  have h5 := frame_cancel ((J.G i).FX ((J.G i).s + 1) le_rfl) ((Matrix.mul_assoc _ _ _).symm.trans h4)
  have h6 := Chain.xiPen_mk (J.E i).adapt (((J.E i).rep_bij _ 0 rfl).mapsTo (Set.mem_univ (α i)))
    (κ.val.toBlocks₁₁ *ᵥ ownVec J.A (J.G i) (J.P i) e (J.ι _ γ))
  refine Eq.symm ?_
  refine (congrArg₂ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).xiPen _ _) h2 h5.symm).trans ((h6 _).trans ((h3 _ _ _).trans ?_))
  refine (congrArg (c * ·) hA).trans ?_
  simp only [locXi, dif_neg (show ¬ (J.G i).s + 2 < B.R.m by omega), dif_pos hs, sgnAt]
  ring

theorem facAt_top (hW : AllTrue W) (ha : a.Is) (haT : a.True)
    (hiA : ∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) (hJ : J.Reads) (hj : (J.G i).s + 1 + 1 ≤ B.R.m) (e')
    (he' : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e') (α : J.Ch ((J.G i).s + 1)) (γ : J.Ch ((J.G i).s + 1 + 1)) (c : ℂ) (hc0 : c ≠ 0)
    (hc : MoveAt J i e' (Nat.le_of_succ_le hj) (J.ι _ α) c) : FacAt J i ((J.G i).s + 1) hj α γ c⁻¹ := by
  refine isLocFac_of (J.G i).q (J.G i).unit (J.G i).idem (J.G i).compl.dense _ ((J.G i).FX _ le_rfl) (J.G i).FM
    (a.g.x _).L (a.g.x _).L (ha.x _ (Nat.le_of_succ_le hj)).sd (ha.x _ hj).sd (haT.pinX.xs _ (Nat.le_of_succ_le hj)).2.2
    (haT.pinX.xs _ hj).2.2 ((J.G i).latX _ _) (J.G i).latM _ _
    (xiTop_mem_SB _ (J.E i).reg (J.G i).cond (J.G i).unitVol _ ((J.E i).cos (α i)))
    ((J.E i).dL_top (α i) (γ i)) _ fun z => ?_
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  obtain ⟨e, he⟩ := exists_topOrd B.R (J.G i).s hs
  obtain ⟨κ, h1, h2, -, h3⟩ := hc
  rw [hJ.sec _ (Nat.le_of_succ_le hj)] at h2
  have h4 := toLoc_frames ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (rankN (I.rec7 l Z) _ (Nat.le_of_succ_le hj))
    (rankN (I.rec7 l Z) _ hj) e e' _ _ z _ _ (GlobalTheory.T.true_geometry_row_pair_value W hW u a ha haT hiA t J hJ i hj (J.ι _ γ) e he) h1
  have h5 := (frame_cancel (J.G i).FM h4).trans (Matrix.mul_assoc _ _ _).symm
  have hmem := ownVec_mem J.A (G := J.G i) (J.P i) (hJ.tw i).nmem (hJ.tw i).compl e' (J.ι _ α)
  have hA := (lastAgree_at (i := i) hW hJ).2 e' (e.trans (finCongr (congrArg B.R.N hs))) he' (fun r => he r)
    (castSp B.fields.E (congrArg B.R.N hs) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ α)).1.1 (J.P i))
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ γ)).1.1 (J.P i)) (homOf I l Z _ hj z))
    ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ α)).1.1 (J.P i)).symm (Formalism.L2.Col.repY (J.A.p0 _ (J.ι _ α)).1.2))
    (fun n => ?_)
  · refine Eq.symm ((eq_inv_mul_iff_mul_eq₀ hc0).2 ?_)
    rw [h2]
    refine (h3 _ _ _ _ _).symm.trans ?_
    rw [← hJ.M i] at hA
    refine Eq.trans ?_ (hA.trans ?_)
    · exact congrArg _ (h5.symm.trans rfl)
    · simp only [locXi, dif_neg (show ¬ (J.G i).s + 1 + 2 < B.R.m by omega), dif_neg (show ¬ (J.G i).s + 1 + 2 = B.R.m by omega),
        dif_pos hs]
      rfl
  · obtain ⟨r, rfl⟩ := e'.surjective n
    have h6 := hmem r
    have hcp := (hJ.tw i).compl
    refine (hcp.int _).1 ?_
    have h7 : 0 < valuation (J.G i).k (((J.G i).ϖ : (J.G i).k) ^ (I.cst (W.P.I.tup t)).M) := by
      rw [map_pow]
      exact pow_pos ((Valuation.pos_iff _).2 (J.G i).ϖ.ne_zero) _
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, ← mul_one (_⁻¹), le_inv_mul_iff₀ h7] at h6
    rw [map_mul, map_pow, ← hcp.unif, Valuation.mem_integer_iff, map_mul]
    exact h6

theorem sgnAt_mul (hJ : J.Reads) (j : ℕ) (hj : j < B.R.m) (β : J.Ch₀ j) {n n' : ℕ} (h : Even (n + n')) :
    sgnAt J i j hj β n * sgnAt J i j hj β n' = 1 := by
  unfold sgnAt GlobalTheory.TwBridge.sgn
  show J.sg i ^ _ * J.sg i ^ _ = 1
  rcases hJ.sg i with h1 | h1 <;> rw [h1]
  · simp
  · rw [← zpow_add₀ (by norm_num), ← mul_add]
    refine Even.neg_one_zpow (Even.mul_left ?_ _)
    exact_mod_cast h

theorem sgnAt_rou (hJ : J.Reads) (j : ℕ) (hj : j < B.R.m) (β : J.Ch₀ j) (n : ℕ) :
    ∃ N : ℕ, 0 < N ∧ sgnAt J i j hj β n ^ N = 1 :=
  ⟨2, two_pos, by rw [sq, sgnAt_mul hJ j hj β ⟨n, rfl⟩]⟩

theorem even_ranks (R : Ranks) (j : ℕ) (h : j + 2 < R.m) :
    Even (R.N j + Formalism.L2.Col.cOf R j + (R.N (j + 1 + 1) + Formalism.L2.Col.cOf R (j + 1 + 1))) := by
  obtain ⟨c, hc⟩ : ∃ c, R.m = j + 3 + c := ⟨R.m - (j + 3), by omega⟩
  have e1 : Formalism.L2.Col.cOf R j = c + 2 := by unfold Formalism.L2.Col.cOf; omega
  have e2 : Formalism.L2.Col.cOf R (j + 1 + 1) = c := by unfold Formalism.L2.Col.cOf; omega
  rw [e1, e2]
  show Even (R.k + j * (R.t + 1) + (c + 2) + (R.k + (j + 1 + 1) * (R.t + 1) + c))
  exact ⟨R.k + (j + 1) * (R.t + 1) + c + 1, by ring⟩

theorem chart_zero_eq (α α' : J.Ch 0) : α = α' := funext fun n => by
  have hb := (J.E n).rep_bij 0 (J.G n).s (Nat.zero_add _)
  have h1 := hb.mapsTo (Set.mem_univ (α n))
  have h2 := hb.mapsTo (Set.mem_univ (α' n))
  rw [(J.E n).reps.zero] at h1 h2
  exact hb.injOn (Set.mem_univ _) (Set.mem_univ _) (h1.trans h2.symm)

variable (i) in

theorem exists_signs_at (hW : AllTrue W) (ha : a.Is) (haT : a.True)
    (hiA : ∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) (hJ : J.Reads) :
    ∃ (σ : ∀ j, J.Ch₀ j → ℂ) (τ : ∀ j, J.Ch₀ (j + 1) → ℂ), (∀ j β, ∃ n : ℕ, 0 < n ∧ σ j β ^ n = 1) ∧
      (∀ j β, ∃ n : ℕ, 0 < n ∧ τ j β ^ n = 1) ∧ (∀ j, j + 1 < B.R.m → ∀ β, τ j β * σ (j + 1) β = 1) ∧
      ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch j) (γ : J.Ch (j + 1)), FacAt J i j hj α γ (σ j (J.ι j α) * τ j (J.ι (j + 1) γ)) := by
  have hm := GlobalTheory.T.true_geometry_twist_local_bound W hW u a ha haT t J hJ i
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  obtain ⟨e, he⟩ := exists_xOrd B.R ((J.G i).s + 1)
  choose c hc hc' using exists_moveAt hm e he (by omega)
  have hc0 : ∀ β, c β ≠ 0 := fun β h => by
    obtain ⟨n, hn, h1⟩ := hc β
    rw [h, zero_pow hn.ne'] at h1
    exact zero_ne_one h1
  let C : ∀ j, J.Ch₀ j → ℂ := fun j β => if h : j = (J.G i).s + 1 then c (h ▸ β) else 1
  have hC : ∀ β, C ((J.G i).s + 1) β = c β := fun β => dif_pos rfl
  have hCr : ∀ j β, ∃ n : ℕ, 0 < n ∧ C j β ^ n = 1 := fun j β => by
    by_cases h : j = (J.G i).s + 1
    · subst h
      rw [hC]
      exact hc β
    · exact ⟨1, one_pos, by simp only [C, dif_neg h, one_pow]⟩
  refine ⟨fun j β => if h : j + 1 < B.R.m then sgnAt J i j (by omega) β (B.R.N (j + 1) + Formalism.L2.Col.cOf B.R (j + 1)) else (C j β)⁻¹,
    fun j β => if h : j + 2 < B.R.m then sgnAt J i (j + 1) (by omega) β (B.R.N j + Formalism.L2.Col.cOf B.R j) else C (j + 1) β,
    fun j β => ?_, fun j β => ?_, fun j hj β => ?_, fun j hj α γ => ?_⟩
  · beta_reduce
    split_ifs
    · exact sgnAt_rou hJ _ _ _ _
    · exact rou_inv (hCr j β)
  · beta_reduce
    split_ifs
    · exact sgnAt_rou hJ _ _ _ _
    · exact hCr _ β
  · beta_reduce
    by_cases h : j + 2 < B.R.m
    · rw [dif_pos h, dif_pos (show j + 1 + 1 < B.R.m from h)]
      exact sgnAt_mul hJ _ _ _ (even_ranks B.R j h)
    · rw [dif_neg h, dif_neg (show ¬ j + 1 + 1 < B.R.m from h)]
      obtain rfl : j = (J.G i).s := by omega
      rw [hC]
      exact mul_inv_cancel₀ (hc0 β)
  · beta_reduce
    rcases lt_trichotomy (j + 2) B.R.m with h | h | h
    · rw [dif_pos h, dif_pos (show j + 1 < B.R.m by omega)]
      exact facAt_mid hW ha haT hJ hm j ((J.G i).s - (j + 1)) (by omega) hj _ α γ
    · obtain rfl : j = (J.G i).s := by omega
      rw [dif_neg (show ¬ (J.G i).s + 2 < B.R.m by omega), dif_pos (show (J.G i).s + 1 < B.R.m by omega), hC]
      exact facAt_pen hW ha haT hJ hm hj e he α γ _ (hc' _)
    · obtain rfl : j = (J.G i).s + 1 := by omega
      rw [dif_neg (show ¬ (J.G i).s + 1 + 2 < B.R.m by omega), dif_neg (show ¬ (J.G i).s + 1 + 1 < B.R.m by omega), hC]
      have h1 : C ((J.G i).s + 1 + 1) (J.ι _ γ) = 1 := dif_neg (by omega)
      rw [h1, mul_one]
      exact facAt_top hW ha haT hiA hJ hj e he α γ _ (hc0 _) (hc' _)

theorem idem_union (hW : AllTrue W) (ha : a.Is) (haT : a.True) (hJ : J.Reads) {e₀ : AE (I.rec7 l Z)}
    (he₀ : IsIdemSum e₀ ((B.primes X).vT u ∪ (B.primes X).vGs)) :
    ∃ Q : Finset (Formalism.L2.DIV.Pl (I.rec7 l Z).host.E), (∀ PP, PP ∈ Q ↔ ∃ n, J.pl n = PP) ∧
      Disjoint ((B.primes X).vT u ∪ (B.primes X).vGs) Q ∧
      IsIdemSum (e₀ + ∑ n, (J.G n).q.e) (((B.primes X).vT u ∪ (B.primes X).vGs) ∪ Q) := by
  have hI : I.Ok := hW.tr.ok
  have hPr := l.pr
  have hd : Disjoint ((B.primes X).vT u) (Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup (W.P.I.tup t))) :=
    Finset.disjoint_left.2 fun P h1 h2 =>
      GlobalTheory.Proof.NarrowJetMoments.notMem_rowSG hPr hI.sel_ok (hPr.T_prime u) (hI.T_mem u) (hPr.T_ne_g u) h2
        (GlobalTheory.Mem.Col2.T_mem_vT hPr u ⟨P, h1⟩)
  have hgq : Disjoint (B.primes X).vGs
      (Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K)) :=
    GlobalTheory.NormOneUnit.disjoint_vGs_QE (I.tup (W.P.I.tup t)) hPr hI.sel_ok hI.g_mem
  have hid := hJ.is.idem
  have hS : Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup (W.P.I.tup t)) u =
      ((B.primes X).vT u ∪ (B.primes X).vGs) ∪
        Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := by
    simp only [Formalism.L2.Col.Sall, Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG, Finset.union_assoc]
  rw [hS] at hid
  obtain ⟨e₁, h1, h2⟩ := GlobalTheory.T.true_geometry_twist_quadratic_level W hW u a ha haT t J hJ
  obtain rfl : e₀ = e₁ := (GlobalTheory.ExportSeries.idem_eq he₀).symm.trans (GlobalTheory.ExportSeries.idem_eq h1)
  refine ⟨_, fun PP => ⟨fun h => hJ.surj PP ((hW.tq.Q t PP).2 h), ?_⟩,
    Finset.disjoint_union_left.2 ⟨hd.mono_right Finset.subset_union_right, hgq⟩, h2 ▸ hid⟩
  rintro ⟨n, rfl⟩
  exact (hW.tq.Q t _).1 (J.mem n)

end Steps

theorem ratDatum_add_twist_places : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ t (J : QJ a t), J.Reads → ∃ (p : ∀ j, J.Ch j → ℂ) (q : ∀ j, J.Ch (j + 1) → ℂ), (∀ j, j < B.R.m → ∀ α, ∃ n : ℕ, 0 < n ∧ (p j α * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ)) ^ n = 1) ∧ (∀ j, j < B.R.m → ∀ γ, ∃ n : ℕ, 0 < n ∧ (q j γ * ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹) ^ n = 1) ∧ (∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ ∀ α, p 0 α * (J.A.chr 1 (J.A.xr 0 (J.ι 0 α)) : ℂ) = c) ∧ (∀ j, j + 1 < B.R.m → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ ∀ γ, q j γ * ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹ * (p (j + 1) γ * (J.A.chr (j + 1 + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ)) = c) ∧ ∀ e₀ : AE (I.rec7 l Z), IsIdemSum e₀ ((B.primes X).vT u ∪ (B.primes X).vGs) → ∀ j (hj : j + 1 ≤ B.R.m) α γ (Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ) (f : WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ), IsRatDatum (pk W).ψ _ _ e₀ Ξ (a.g.vac j) f → IsRatDatum (pk W).ψ _ _ (e₀ + ∑ i, (J.G i).q.e) (fun z => Ξ z * (p j α * q j γ * ∏ i, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z)))) (a.g.vac j) (comb (pk W).ψ _ _ (aconv (List.ofFn fun i => (J.E i).dL j (α i) (γ i))) f) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT hiA t J hJ
  choose σ τ hσ hτ hστ hloc using fun i => exists_signs_at (J := J) i hW ha haT hiA hJ
  have hcob := GlobalTheory.T.true_geometry_twist_local_identity W hW u a ha haT t J hJ
  have hm := B.R.two_le_m
  obtain ⟨hP⟩ := hW.tr.pins
  have hc : ∀ j, j < B.R.m → ∀ i, i ≤ B.R.m → ∀ β, ∃ n : ℕ, 0 < n ∧ ((J.A.chr (j + 1) (J.A.xr i β) : ℂ)) ^ n = 1 :=
    fun j hj i hi β => rou_circle (GlobalTheory.T.tupleCharacter_at_basePointDetRoot_rootOfUnity I hW.tr.ok hP l Z u _ J.Ch₀ J.A hJ.is j hj i hi β)
  have c1 : ∀ j, j < B.R.m → ∀ α : J.Ch j, ∃ n : ℕ, 0 < n ∧
      ((∏ i, σ i j (J.ι j α)) * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ)) ^ n = 1 :=
    fun j hj α => rou_mul (rou_prod _ _ fun i _ => hσ i j _) (hc j hj j hj.le _)
  refine ⟨fun j α => ∏ i, σ i j (J.ι j α), fun j γ => ∏ i, τ i j (J.ι (j + 1) γ), c1, ?_, ?_, ?_, ?_⟩
  · intro j hj γ
    exact rou_mul (rou_prod _ _ fun i _ => hτ i j _) (rou_inv (hc j hj (j + 1) (by omega) _))
  · by_cases hne : Nonempty (J.Ch 0)
    · obtain ⟨α₀⟩ := hne
      exact ⟨_, c1 0 (by omega) α₀, fun α => by rw [chart_zero_eq α α₀]⟩
    · exact ⟨1, ⟨1, one_pos, one_pow 1⟩, fun α => (hne ⟨α⟩).elim⟩
  · intro j hj
    have hqp : ∀ γ : J.Ch (j + 1), (∏ i, τ i j (J.ι (j + 1) γ)) * ∏ i, σ i (j + 1) (J.ι (j + 1) γ) = 1 := by
      intro γ
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ => hστ i j hj _
    by_cases hne : Nonempty (J.Ch (j + 1))
    · obtain ⟨γ₀⟩ := hne
      refine ⟨_, rou_mul (hc (j + 1) hj (j + 1) hj.le (J.ι _ γ₀)) (rou_inv (hc j (by omega) (j + 1) (by omega) (J.ι _ γ₀))),
        fun γ => ?_⟩
      have h1 := congrArg (fun x : Circle => (x : ℂ)) (hcob j hj (J.ι _ γ) (J.ι _ γ₀))
      simp only [Circle.coe_mul, Circle.coe_inv] at h1
      calc _ = ((∏ i, τ i j (J.ι (j + 1) γ)) * ∏ i, σ i (j + 1) (J.ι (j + 1) γ)) *
            ((J.A.chr (j + 1 + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ) *
              ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹) := by ring
        _ = _ := by rw [hqp γ, one_mul, h1]
    · exact ⟨1, ⟨1, one_pos, one_pow 1⟩, fun γ => (hne ⟨γ⟩).elim⟩
  · intro e₀ he₀ j hj α γ Ξ f hf
    have hv := GlobalTheory.Fam.VacTheta.main W hW u a ha haT j hj
    obtain ⟨Q, hQ, hdis, hsum⟩ := idem_union hW ha haT hJ he₀
    have key := GlobalTheory.T.rationalDatum_foldr_local_combinations (I.rec7 l Z) (pk W).ψ haT.pinX.std _ _ _ Q J.r J.pl hJ.inj hQ hdis
      (fun i => (J.E i).dL j (α i) (γ i)) _ (fun i => (hloc i j hj α γ).1) (a.g.x j).L (a.g.x (j + 1)).L
      (ha.x j (Nat.le_of_succ_le hj)).sd (ha.x (j + 1) hj).sd (Set.ext (haT.pinX.xs j (Nat.le_of_succ_le hj)).2.2)
      (Set.ext (haT.pinX.xs (j + 1) hj).2.2) Ξ (a.g.vac j) f hv.1 hv.2.1
      (fun e₁ he₁ => ((GlobalTheory.ExportSeries.idem_eq he₀).symm.trans (GlobalTheory.ExportSeries.idem_eq he₁)) ▸ hf) _ hsum
    have hfold := GlobalTheory.QFinLaw.comb_aconv_map (pk W).ψ (fun i => (J.G i).q.v)
      (GlobalTheory.TopVol.TwistPlaces.places_injective W hW u a ha haT t J hJ) (fun i => (J.E i).dL j (α i) (γ i))
      (fun i => (hloc i j hj α γ).2) f _ (List.nodup_finRange J.r)
    rw [List.ofFn_eq_map]
    refine hfold ▸ ?_
    convert key using 2 with z
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

end GlobalTheory.TwPlaces
end
end
