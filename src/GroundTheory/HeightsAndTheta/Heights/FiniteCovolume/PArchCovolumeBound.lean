module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StArchCovolumeBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordEmbedBasis
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StIntegralFormCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StTraceHermNondegenerate
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StDualLatticeMultiple
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordLatticeFullRank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
theorem ArchCovolumeBound.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : CoordEmbedBasis.Statement E ι)
    (h₂ : IntegralFormCovolume.Statement (ι → E) (InfinitePlace E → ι → ℂ)
      (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E)))
    (h₃ : TraceHermNondegenerate.Statement h v) (h₄ : DualLatticeMultiple.Statement h)
    (h₅ : CoordLatticeFullRank.Statement v) : ArchCovolumeBound.Statement h v := by
  intro D
  obtain ⟨k, hk0, hk⟩ := h₄ D
  let e := Pi.basis fun _ : ι => integralBasis E
  obtain ⟨C, hC⟩ := h₂ (coordEmbed E ι) e (traceHerm h v) volume (Measure.pi.isAddHaarMeasure _) h₃ h₁.1
    (by rw [h₁.2, finrank_eq_card_basis e])
  refine ⟨Real.sqrt (C * |(k : ℝ)| ^ Fintype.card (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E))),
    fun La hLa => ?_⟩
  let φ : W →+ (ι → E) := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
  have hφ : ∀ x, v.equivFun.symm (φ x) = x := fun x => v.equivFun.symm_apply_apply x
  have hmem : ∀ y, y ∈ La.map φ ↔ v.equivFun.symm y ∈ La := by
    intro y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [hφ]
    · intro hy
      exact ⟨_, hy, v.equivFun.apply_symm_apply y⟩
  have harch : archLattice v La = AddSubgroup.toIntSubmodule ((La.map φ).map (coordEmbed E ι)) := by
    rw [archLattice, AddSubgroup.map_map]
    rfl
  obtain ⟨hfg, hspan⟩ := h₅ La hLa.isLattice
  obtain ⟨hint, hdual⟩ := hk La hLa
  obtain ⟨hD, hZ, hcov⟩ := hC (La.map φ) k hk0 hfg hspan
    (fun x hx y hy => hint _ ((hmem x).1 hx) _ ((hmem y).1 hy))
    (fun y hy => by
      rw [hmem, map_zsmul]
      refine hdual _ fun x hx => ?_
      obtain ⟨n, hn⟩ := hy (φ x) (AddSubgroup.mem_map_of_mem φ hx)
      exact ⟨n, by rw [traceHerm_apply, hφ] at hn; exact hn⟩)
  rw [harch]
  exact ⟨hD, hZ, (le_abs_self _).trans (Real.abs_le_sqrt hcov)⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
