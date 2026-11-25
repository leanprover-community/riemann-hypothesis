module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7}

theorem ell_vecMul_last {σ n : ℕ} (b : Mx D (σ + 1) n) : ell D (σ + 1) ᵥ* b = b (Fin.last σ) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, ell]
  rw [Finset.sum_eq_single (Fin.last σ)]
  · simp
  · intro i _ hi
    rw [ite_eq_right (fun h => hi (Fin.ext (by simp only [Fin.val_last]; omega))), zero_mul]
  · simp

theorem zEll_mul_eq {σ n : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) (b : Mx D (σ + 1) n) :
    zEll L (σ + 1) ζ ⬝ b = vecMulVec (ratV ζ) (b (Fin.last σ)) := by
  rw [zEll, Matrix.vecMulVec_mul, ell_vecMul_last]

def splitLine {σ n : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) (i₀ : Fin L.rank) (h1 : ∀ i : Fin L.rank, i = i₀)
    (h0 : ζ i₀ ≠ 0) : Mx D (σ + 1) n ≃+ Mx D σ n × Mx D L.rank n where
  toFun b := (Matrix.of fun i j => b (Fin.castSucc i) j, zEll L (σ + 1) ζ ⬝ b)
  invFun p := Matrix.of fun i j => Fin.lastCases (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) i
  left_inv b := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Matrix.of_apply, Fin.lastCases_last, zEll_mul_eq, vecMulVec_apply, ratV]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]
    · simp
  right_inv p := by
    refine Prod.ext ?_ ?_
    · ext i j; simp
    · ext k j
      simp only [zEll_mul_eq, vecMulVec_apply, ratV, Matrix.of_apply, Fin.lastCases_last]
      rw [h1 k, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]
  map_add' b b' := Prod.ext (by ext i j; simp) (Matrix.mul_add _ _ _)

theorem continuous_splitLine {σ n : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) (i₀ : Fin L.rank)
    (h1 : ∀ i : Fin L.rank, i = i₀) (h0 : ζ i₀ ≠ 0) :
    Continuous (splitLine (σ := σ) (n := n) L ζ i₀ h1 h0) ∧ Continuous (splitLine (σ := σ) (n := n) L ζ i₀ h1 h0).symm := by
  constructor
  · refine Continuous.prodMk ?_ (continuous_const.matrix_mul continuous_id)
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply _)
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) i
    · change Continuous fun p : Mx D σ n × Mx D L.rank n => Fin.lastCases (motive := fun _ => AE D)
        (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.last σ)
      simp only [Fin.lastCases_last]
      fun_prop
    · change Continuous fun p : Mx D σ n × Mx D L.rank n => Fin.lastCases (motive := fun _ => AE D)
        (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.castSucc i)
      simp only [Fin.lastCases_castSucc]
      fun_prop

theorem fourierBesselBasePoint_mul_eq_gen {σ : ℕ} {V V₀ A L : HSp D} (d : HypDec V V₀ σ) (o : OrthDec V₀ A L)
    (ζ : Fin L.rank → D.host.E) (S : HSp D) (b : Mx D (σ + 1) S.rank) :
    xLast d (vecB o ζ) ⬝ b = d.incX S (Matrix.of fun i j => b (Fin.castSucc i) j) +
      d.inc0 S ((o.resT S).symm (0, zEll L (σ + 1) ζ ⬝ b)) := by
  rw [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, zEll_mul_eq,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, OrthDec.jB, ← ratV_mulVec]
  ext k j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, xLast, vecMulVec_apply, vecB]

theorem fourierBesselBasePoint_mul_eq {σ : ℕ} (B : BesLev D σ) (S : HSp D) (b : Mx D (σ + 1) S.rank) :
    x0 B ⬝ b = B.d.incX S (Matrix.of fun i j => b (Fin.castSucc i) j) +
      B.d.inc0 S ((B.o.resT S).symm (0, zl B ⬝ b)) :=
  fourierBesselBasePoint_mul_eq_gen B.d B.o B.ζ S b

theorem heisSymplecticHalf_fourierBesselBasePoint_mul_gen {σ : ℕ} {V V₀ A L : HSp D} (d : HypDec V V₀ σ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (S : HSp D) (b b' : Mx D (σ + 1) S.rank) :
    symplOH S V (xLast d (vecB o ζ) ⬝ b) (xLast d (vecB o ζ) ⬝ b') =
      symplOH S L (zEll L (σ + 1) ζ ⬝ b) (zEll L (σ + 1) ζ ⬝ b') := by
  rw [fourierBesselBasePoint_mul_eq_gen, fourierBesselBasePoint_mul_eq_gen]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX,
    HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, HypDec.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, zero_add]
  rw [symplOH_skew S V (d.incX S _) (d.inc0 S _), HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero, zero_add,
    OrthDec.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem heisSymplecticHalf_fourierBesselBasePoint_mul {σ : ℕ} (B : BesLev D σ) (S : HSp D) (b b' : Mx D (σ + 1) S.rank) :
    symplOH S B.V (x0 B ⬝ b) (x0 B ⬝ b') = symplOH S B.L (zl B ⬝ b) (zl B ⬝ b') :=
  heisSymplecticHalf_fourierBesselBasePoint_mul_gen B.d B.o B.ζ S b b'

theorem zEll_mem_ratMx {σ : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) : zEll L (σ + 1) ζ ∈ ratMx D L.rank (σ + 1) := by
  refine ⟨vecMulVec ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  refine Matrix.ext fun k i => ?_
  change incA D (ζ k * (if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0)) =
    incA D (ζ k) * (if i.1 + 1 = σ + 1 then (1 : AE D) else 0)
  split_ifs
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, map_zero]

theorem zl_mem_ratMx {σ : ℕ} (B : BesLev D σ) : zl B ∈ ratMx D B.L.rank (σ + 1) :=
  zEll_mem_ratMx B.L B.ζ

theorem fourierBesselBasePoint_mul_mem_rationalAdelicMatrix_gen {σ : ℕ} {V V₀ A L : HSp D} (d : HypDec V V₀ σ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (S : HSp D) {γ : Mx D (σ + 1) S.rank}
    (hγ : γ ∈ ratMx D (σ + 1) S.rank) :
    xLast d (vecB o ζ) ⬝ γ ∈ ratMx D V.rank S.rank := by
  rw [fourierBesselBasePoint_mul_eq_gen]
  obtain ⟨g, rfl⟩ := hγ
  refine add_mem (ratMx_mul (rat_mem _) ⟨Matrix.of fun i j => g (Fin.castSucc i) j, rfl⟩)
    (ratMx_mul (rat_mem _) ?_)
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  exact ratMx_mul (rat_mem _) (ratMx_mul (zEll_mem_ratMx L ζ) (rat_mem _))

theorem fourierBesselBasePoint_mul_mem_rationalAdelicMatrix {σ : ℕ} (B : BesLev D σ) (S : HSp D) {γ : Mx D (σ + 1) S.rank} (hγ : γ ∈ ratMx D (σ + 1) S.rank) :
    x0 B ⬝ γ ∈ ratMx D B.V.rank S.rank :=
  fourierBesselBasePoint_mul_mem_rationalAdelicMatrix_gen B.d B.o B.ζ S hγ

theorem splitLine_symm_mem {σ n : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) (i₀ : Fin L.rank)
    (h1 : ∀ i : Fin L.rank, i = i₀) (h0 : ζ i₀ ≠ 0) {p : Mx D σ n × Mx D L.rank n}
    (hp : p ∈ (ratMx D σ n).prod (ratMx D L.rank n)) :
    (splitLine L ζ i₀ h1 h0).symm p ∈ ratMx D (σ + 1) n := by
  obtain ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ := hp
  refine ⟨Matrix.of fun i j => Fin.lastCases ((ζ i₀)⁻¹ * g₂ i₀ j) (fun i => g₁ i j) i, ?_⟩
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i
  · change incA D (Fin.lastCases (motive := fun _ => D.host.E) ((ζ i₀)⁻¹ * g₂ i₀ j) (fun i => g₁ i j) (Fin.last σ)) =
      Fin.lastCases (motive := fun _ => AE D) (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.last σ)
    rw [Fin.lastCases_last, Fin.lastCases_last, map_mul, ← hg₂]; rfl
  · change incA D (Fin.lastCases (motive := fun _ => D.host.E) ((ζ i₀)⁻¹ * g₂ i₀ j) (fun i => g₁ i j) (Fin.castSucc i)) =
      Fin.lastCases (motive := fun _ => AE D) (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.castSucc i)
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc, ← hg₁]; rfl

theorem splitLine_mem {σ n : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) (i₀ : Fin L.rank)
    (h1 : ∀ i : Fin L.rank, i = i₀) (h0 : ζ i₀ ≠ 0) {b : Mx D (σ + 1) n} (hb : b ∈ ratMx D (σ + 1) n) :
    splitLine L ζ i₀ h1 h0 b ∈ (ratMx D σ n).prod (ratMx D L.rank n) := by
  obtain ⟨g, rfl⟩ := hb
  exact ⟨⟨Matrix.of fun i j => g (Fin.castSucc i) j, rfl⟩, ratMx_mul (zEll_mem_ratMx L ζ) (rat_mem _)⟩

theorem heis_base_gen (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (σ : ℕ) (S : HSp D)
    (V V₀ A L : HSp D) (d : HypDec V V₀ σ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)
    (hline : IsLineVec L ζ)
    (vB : VolM D (σ + 1) S.rank) (vT : VolM D σ S.rank) (vL : VolM D L.rank S.rank)
    (f : WO S V → ℂ) (y : WO S L → ℂ) (hf : Quasi ψ S V f) (hy : Quasi ψ S L y) :
    (∫ b in vB.𝓕, f (xLast d (vecB o ζ) ⬝ b) * star (y (zEll L (σ + 1) ζ ⬝ b)) ∂vB.μ =
      contractT o S vL.μ vL.𝓕 (d.mixT S ψ vT.μ vT.𝓕 f 0) y 0) ∧
    ∫⁻ v in vL.𝓕, ‖d.mixT S ψ vT.μ vT.𝓕 f 0 ((o.resT S).symm (0, v))‖ₑ ∂vL.μ ≤
      ∫⁻ b in vB.𝓕, ‖f (xLast d (vecB o ζ) ⬝ b)‖ₑ ∂vB.μ := by
  have hψn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have hL1 : L.rank = 1 := hline.1
  let i₀ : Fin L.rank := ⟨0, by omega⟩
  have h1 : ∀ i : Fin L.rank, i = i₀ := fun i => Fin.ext (by have := i.2; simp only [i₀]; omega)
  have h0 : ζ i₀ ≠ 0 := by
    intro h
    apply hline.2
    have : ζ = 0 := funext fun i => by rw [h1 i, h]; rfl
    rw [this]; simp
  set e := splitLine (σ := σ) (n := S.rank) L ζ i₀ h1 h0 with he_def
  obtain ⟨he, hes⟩ := continuous_splitLine (σ := σ) (n := S.rank) L ζ i₀ h1 h0
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D (σ + 1) S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D σ S.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D L.rank S.rank
  haveI : BorelSpace (Mx D (σ + 1) S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D σ S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D L.rank S.rank) := ⟨rfl⟩
  haveI : Countable (ratMx D (σ + 1) S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := vT.covol.1
  haveI := vL.covol.1
  haveI := vB.covol.1

  have hx : ∀ b : Mx D (σ + 1) S.rank, xLast d (vecB o ζ) ⬝ b = d.incX S (e b).1 + d.inc0 S ((o.resT S).symm (0, (e b).2)) :=
    fun b => fourierBesselBasePoint_mul_eq_gen d o ζ S b

  set P := vT.μ.prod vL.μ with hP
  let me : Mx D (σ + 1) S.rank ≃ᵐ Mx D σ S.rank × Mx D L.rank S.rank :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving me (P.map e.symm) P := MeasurePreserving.symm me.symm ⟨me.symm.measurable, rfl⟩
  have hmp' : MeasurePreserving e (P.map e.symm) P := hmp
  have hν : (P.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map P e.symm hes (by simpa using he)
  have hPF : IsAddFundamentalDomain ((ratMx D σ S.rank).prod (ratMx D L.rank S.rank)) (vT.𝓕 ×ˢ vL.𝓕) P :=
    GlobalTheory.CoordUnfold.isAddFundamentalDomain_prod vT.covol.2.1 vL.covol.2.1
  have hF' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) (P.map e.symm) := by
    let g : (ratMx D σ S.rank).prod (ratMx D L.rank S.rank) → ratMx D (σ + 1) S.rank :=
      fun p => ⟨e.symm p, splitLine_symm_mem L ζ i₀ h1 h0 p.2⟩
    have hg : Function.Bijective g := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, splitLine_mem L ζ i₀ h1 h0 x.2⟩, Subtype.ext (by simp [g])⟩
    refine hPF.preimage_of_equiv hmp'.quasiMeasurePreserving hg ?_
    intro p x
    simp [g, AddSubgroup.vadd_def]
  have hv : (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) = 1 := by
    refine (hmp.measure_preimage_equiv _).trans ?_
    rw [Measure.prod_prod, vT.covol.2.2, vL.covol.2.2, one_mul]
  have hcov : IsCovolOne (ratMx D (σ + 1) S.rank) (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) := ⟨hν, hF', hv⟩
  have hμeq : P.map e.symm = vB.μ := covolOne_measure_eq vB.covol hcov

  have hfx : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b,
      f (xLast d (vecB o ζ) ⬝ (γ + b)) = ψ (-(symplOH S V (xLast d (vecB o ζ) ⬝ γ) (xLast d (vecB o ζ) ⬝ b))) * f (xLast d (vecB o ζ) ⬝ b) := by
    intro γ hγ b
    obtain ⟨δ, hδ⟩ := fourierBesselBasePoint_mul_mem_rationalAdelicMatrix_gen d o ζ S hγ
    have e1 := hf.1 δ (xLast d (vecB o ζ) ⬝ b)
    rw [show ratW V S δ = xLast d (vecB o ζ) ⬝ γ from hδ] at e1
    rw [Matrix.mul_add, e1]
  have hyz : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b,
      y (zEll L (σ + 1) ζ ⬝ (γ + b)) = ψ (-(symplOH S L (zEll L (σ + 1) ζ ⬝ γ) (zEll L (σ + 1) ζ ⬝ b))) * y (zEll L (σ + 1) ζ ⬝ b) := by
    intro γ hγ b
    obtain ⟨δ, hδ⟩ := ratMx_mul (zEll_mem_ratMx L ζ) hγ
    have e1 := hy.1 δ (zEll L (σ + 1) ζ ⬝ b)
    rw [show ratW L S δ = zEll L (σ + 1) ζ ⬝ γ from hδ] at e1
    rw [Matrix.mul_add, e1]
  have hunit : ∀ a, ψ a * star (ψ a) = 1 := fun a => by
    rw [← starRingEnd_apply, RCLike.mul_conj, hψn]; simp
  set s := vT.𝓕 ×ˢ vL.𝓕 with hs
  set G : Mx D (σ + 1) S.rank → ℂ := fun b => f (xLast d (vecB o ζ) ⬝ b) * star (y (zEll L (σ + 1) ζ ⬝ b)) with hG
  have hGper : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b, G (γ + b) = G b := by
    intro γ hγ b
    simp only [hG]
    rw [hfx γ hγ b, hyz γ hγ b, heisSymplecticHalf_fourierBesselBasePoint_mul_gen, star_mul]
    calc ψ (-symplOH S L (zEll L (σ + 1) ζ ⬝ γ) (zEll L (σ + 1) ζ ⬝ b)) * f (xLast d (vecB o ζ) ⬝ b) *
          (star (y (zEll L (σ + 1) ζ ⬝ b)) * star (ψ (-symplOH S L (zEll L (σ + 1) ζ ⬝ γ) (zEll L (σ + 1) ζ ⬝ b))))
        = (ψ (-symplOH S L (zEll L (σ + 1) ζ ⬝ γ) (zEll L (σ + 1) ζ ⬝ b)) * star (ψ (-symplOH S L (zEll L (σ + 1) ζ ⬝ γ) (zEll L (σ + 1) ζ ⬝ b)))) *
          (f (xLast d (vecB o ζ) ⬝ b) * star (y (zEll L (σ + 1) ζ ⬝ b))) := by ring
      _ = _ := by rw [hunit, one_mul]
  have hx0c : Continuous fun b : Mx D (σ + 1) S.rank => xLast d (vecB o ζ) ⬝ b := continuous_const.matrix_mul continuous_id
  have hzlc : Continuous fun b : Mx D (σ + 1) S.rank => zEll L (σ + 1) ζ ⬝ b := continuous_const.matrix_mul continuous_id
  have hGc : Continuous G := (hf.2.comp hx0c).mul (continuous_star.comp (hy.2.comp hzlc))
  set H : Mx D σ S.rank × Mx D L.rank S.rank → ℂ :=
    fun p => f (d.incX S p.1 + d.inc0 S ((o.resT S).symm (0, p.2))) * star (y p.2) with hH
  have hGH : ∀ p, G (e.symm p) = H p := by
    intro p
    simp only [hG, hH]
    rw [hx (e.symm p), AddEquiv.apply_symm_apply]
    congr 3
    exact congrArg Prod.snd (e.apply_symm_apply p)
  have hmix : ∀ w₀, d.mixT S ψ vT.μ vT.𝓕 f 0 w₀ = ∫ ξ in vT.𝓕, f (d.incX S ξ + d.inc0 S w₀) ∂vT.μ := by
    intro w₀
    change ∫ ξ in vT.𝓕, heisO ψ S V (d.incX S ξ) (heisO ψ S V (d.incAdj S 0)
      (heisO ψ S V (d.inc0 S w₀) f)) 0 ∂vT.μ = _
    congr 1
    funext ξ
    rw [HypDec.integrandT_eq, map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  have hGi : IntegrableOn G (e ⁻¹' s) (P.map e.symm) := covolOne_integrableOn hcov G hGc hGper
  have hHi : Integrable H ((vT.μ.restrict vT.𝓕).prod (vL.μ.restrict vL.𝓕)) := by
    rw [Measure.prod_restrict]
    have h2 := (hmp.integrableOn_comp_preimage me.measurableEmbedding (f := H) (s := s)).1 (by
      have : H ∘ me = G := funext fun b => by
        rw [Function.comp_apply, ← hGH]
        exact congrArg G (e.symm_apply_apply b)
      rw [this]; exact hGi)
    exact h2
  refine ⟨?_, ?_⟩
  · calc ∫ b in vB.𝓕, f (xLast d (vecB o ζ) ⬝ b) * star (y (zEll L (σ + 1) ζ ⬝ b)) ∂vB.μ = ∫ b in vB.𝓕, G b ∂vB.μ := rfl
      _ = ∫ b in e ⁻¹' s, G b ∂(P.map e.symm) := (covolOne_integral_eq vB.covol hcov G hGper).symm
      _ = ∫ p in s, H p ∂P := by
        have h3 := hmp.setIntegral_preimage_emb me.measurableEmbedding H s
        rw [← h3]
        refine congrArg (fun F : Mx D (σ + 1) S.rank → ℂ => ∫ b in e ⁻¹' s, F b ∂(P.map e.symm)) (funext fun b => ?_)
        rw [← hGH]
        exact (congrArg G (e.symm_apply_apply b)).symm
      _ = ∫ v in vL.𝓕, ∫ ξ in vT.𝓕, H (ξ, v) ∂vT.μ ∂vL.μ := by
        rw [hP, ← Measure.prod_restrict]
        exact integral_prod_symm H hHi
      _ = _ := by
        change _ = ∫ v in vL.𝓕, d.mixT S ψ vT.μ vT.𝓕 f 0 ((o.resT S).symm (0, v)) * star (y v) ∂vL.μ
        congr 1
        funext v
        rw [hmix, ← integral_mul_const]
  · have hψe : ∀ a, ‖ψ a‖ₑ = 1 := fun a => by rw [← ofReal_norm_eq_enorm, hψn, ENNReal.ofReal_one]
    set K : Mx D σ S.rank × Mx D L.rank S.rank → ENNReal :=
      fun p => ‖f (d.incX S p.1 + d.inc0 S ((o.resT S).symm (0, p.2)))‖ₑ with hK
    have hKc : Continuous K := by
      refine (hf.2.comp ?_).enorm
      simp only [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply]
      exact (continuous_const.matrix_mul continuous_fst).add (continuous_const.matrix_mul
        (continuous_const.add (continuous_const.matrix_mul continuous_snd)))
    have hKe : ∀ b, K (e b) = ‖f (xLast d (vecB o ζ) ⬝ b)‖ₑ := fun b => by rw [hK, hx b]
    have hper' : ∀ (γ : ratMx D (σ + 1) S.rank) (b : Mx D (σ + 1) S.rank),
        ‖f (xLast d (vecB o ζ) ⬝ (γ +ᵥ b))‖ₑ = ‖f (xLast d (vecB o ζ) ⬝ b)‖ₑ := by
      intro γ b
      rw [AddSubgroup.vadd_def, vadd_eq_add, hfx γ γ.2 b, enorm_mul, hψe, one_mul]
    have hF'' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' s) vB.μ := hμeq ▸ hF'
    calc ∫⁻ v in vL.𝓕, ‖d.mixT S ψ vT.μ vT.𝓕 f 0 ((o.resT S).symm (0, v))‖ₑ ∂vL.μ
        ≤ ∫⁻ v in vL.𝓕, ∫⁻ ξ in vT.𝓕, K (ξ, v) ∂vT.μ ∂vL.μ := by
          refine lintegral_mono fun v => ?_
          rw [hmix]
          exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p in s, K p ∂P := by
        rw [hP, ← Measure.prod_restrict, lintegral_prod_symm _ hKc.measurable.aemeasurable]
      _ = ∫⁻ b in e ⁻¹' s, K (e b) ∂(P.map e.symm) :=
        (hmp'.setLIntegral_comp_preimage_emb me.measurableEmbedding K s).symm
      _ = ∫⁻ b in e ⁻¹' s, ‖f (xLast d (vecB o ζ) ⬝ b)‖ₑ ∂vB.μ := by
        rw [hμeq]; congr 1; funext b; exact hKe b
      _ = ∫⁻ b in vB.𝓕, ‖f (xLast d (vecB o ζ) ⬝ b)‖ₑ ∂vB.μ := hF''.setLIntegral_eq vB.covol.2.1 _ hper'

theorem heis_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : HSp D) (B : BesLev D σ) (vB : VolM D (σ + 1) S.rank) (vT : VolM D σ S.rank) (vL : VolM D B.L.rank S.rank) (f : WO S B.V → ℂ) (y : WO S B.L → ℂ), Quasi ψ S B.V f → Quasi ψ S B.L y → (∫ b in vB.𝓕, f (x0 B ⬝ b) * star (y (zl B ⬝ b)) ∂vB.μ = contractT B.o S vL.μ vL.𝓕 (B.d.mixT S ψ vT.μ vT.𝓕 f 0) y 0) ∧ ∫⁻ v in vL.𝓕, ‖B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v))‖ₑ ∂vL.μ ≤ ∫⁻ b in vB.𝓕, ‖f (x0 B ⬝ b)‖ₑ ∂vB.μ :=
  fun D ψ hψ σ S B vB vT vL f y hf hy =>
    heis_base_gen D ψ hψ σ S B.V B.V₀ B.A B.L B.d B.o B.ζ B.line vB vT vL f y hf hy

end GlobalTheory.Unf.FB
