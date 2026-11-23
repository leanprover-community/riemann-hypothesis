module

import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.HilbertSquareIntegrableOfSignature
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

section SquareIntegrability

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem hq_umem (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat g ∈ UJset ε :=
  ReciprocityTheory.ChartRestriction.DS.umat_mem_UJset ε g

theorem hq_one (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w)) :
    sigLam ε Ψ T.w (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := by
  have e : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  rw [e]
  exact hrep.1.1

theorem hq_mul (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w)) (a b : Formalism.REAL.UJ ε) :
    sigLam ε Ψ T.w (Formalism.MainNotions.S.umat (a * b)) =
      (sigLam ε Ψ T.w (Formalism.MainNotions.S.umat a)).comp (sigLam ε Ψ T.w (Formalism.MainNotions.S.umat b)) := by
  have e : Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl
  rw [e]
  exact hrep.1.2 _ (hq_umem a) _ (hq_umem b)

theorem hq_iso (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w)) (g : Formalism.REAL.UJ ε) (v : Hlam ε Ψ T.w) :
    ‖sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ :=
  hrep.2.1 _ (hq_umem g) v

theorem hq_memLp_of_ne (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w))
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)) (w₀ x₀ : Hlam ε Ψ T.w) (hx₀ : x₀ ≠ 0)
    (h0 : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) x₀⟫_ℂ) 2 (Formalism.REAL.muG ε))
    (x : Hlam ε Ψ T.w) :
    MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) x⟫_ℂ) 2 (Formalism.REAL.muG ε) :=
  GraphTrick.memLp_of_ne (μ := Formalism.REAL.muG ε) (ρ := fun g : Formalism.REAL.UJ ε => sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g))
    (measurePreserving_mul_right ε) (hq_one hrep) (hq_mul hrep) (hq_iso hrep)
    (Formalism.MainNotions.BridgeCSchur.irr_of hirr) w₀ x₀ hx₀ h0 x

theorem hq_inner
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (y z : Hlam ε Ψ T.w) (g : Formalism.REAL.UJ ε) :
    ⟪y, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) z⟫_ℂ = inner ℂ (y : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) (z : L2 ε)) := by
  rw [Submodule.coe_inner, hcoe _ (hq_umem g)]

theorem hq_w_ne (hP : IsPsiFor ε lam T Ψ) : uniformisationL2 ε Ψ T.w T.w ≠ 0 := by
  have hw : T.w ≠ 0 := by
    intro h
    have h1 : ‖T.w‖ = 1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  exact datumEmbedding_self_ne_zero hP hw

theorem hq_coef_all (hP : IsPsiFor ε lam T Ψ)
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w))
    (hF : ∀ g ∈ UJset ε, ∀ v v' : T.V,
      inner ℂ (uniformisationL2 ε Ψ T.w v') (rreg ε g (uniformisationL2 ε Ψ T.w v)) =
        ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v))
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)) (x : Hlam ε Ψ T.w) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      inner ℂ (uniformisationL2 ε Ψ T.w T.w) (rreg ε (Formalism.MainNotions.S.umat g) (x : L2 ε))) 2 (Formalism.REAL.muG ε) := by
  apply CompanionTheory.RgDs.Hilb.hq_coef_all <;> assumption

theorem hq_sqInt (hP : IsPsiFor ε lam T Ψ)
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w))
    (hF : ∀ g ∈ UJset ε, ∀ v v' : T.V,
      inner ℂ (uniformisationL2 ε Ψ T.w v') (rreg ε g (uniformisationL2 ε Ψ T.w v)) =
        ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v))
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)) :
    Formalism.MainNotions.S.IsSqIntOn ε (sigLam ε Ψ T.w) := by
  apply CompanionTheory.RgDs.Hilb.hq_sqInt <;> assumption

end SquareIntegrability

theorem hilbert_square_integrable_of_signature : StepSig → StepSqInt := by
  intro hS n ε lam T Ψ hP hst hF hirr
  obtain ⟨hcoe, hrep, -⟩ := hS n ε lam T Ψ hP hst
  exact hq_sqInt hP hcoe hrep hF hirr

end PositivityTheory.RgDs.Hilb
