module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

theorem gelf : Gelf := by
  intro K _ _ _ B _ _ _ _ R
  let A0 : StarSubalgebra ℂ (K →L[ℂ] K) := R.range
  have hc : ∀ x y : A0, x * y = y * x := by
    rintro ⟨x, b, rfl⟩ ⟨y, c, rfl⟩
    apply Subtype.ext
    change R b * R c = R c * R b
    rw [← map_mul, ← map_mul, mul_comm]
  let A : StarSubalgebra ℂ (K →L[ℂ] K) := A0.topologicalClosure
  have : IsClosed (A : Set (K →L[ℂ] K)) := A0.isClosed_topologicalClosure
  let cr : CommRing A := A0.commRingTopologicalClosure hc
  let _ : CommCStarAlgebra A :=
    { (inferInstance : CStarAlgebra A) with mul_comm := cr.mul_comm }
  let G := gelfandStarTransform A
  have hmem : ∀ b, R b ∈ A := fun b => A0.le_topologicalClosure ⟨b, rfl⟩
  refine ⟨WeakDual.characterSpace ℂ A, inferInstance, inferInstance, inferInstance,
    A.subtype.comp G.symm.toStarAlgHom, G.toStarAlgHom.comp (R.codRestrict A hmem), ?_, ?_⟩
  · intro f
    have h1 : ‖G (G.symm f)‖ = ‖G.symm f‖ := (gelfandTransform_isometry A).norm_map_of_map_zero (map_zero _) _
    rw [G.apply_symm_apply] at h1
    rw [h1]
    rfl
  · intro b
    change ((G.symm (G ⟨R b, hmem b⟩) : A) : K →L[ℂ] K) = R b
    rw [G.symm_apply_apply]

end PositivityTheory.Rg.BcB.E2.P
