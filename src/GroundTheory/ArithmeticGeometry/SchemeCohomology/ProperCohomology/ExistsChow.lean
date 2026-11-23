module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowMulti
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowSegre
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

noncomputable section

theorem exists_chow' {A : Type u} [CommRing A] [IsNoetherianRing A] (X : Scheme.{u})
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] [IrreducibleSpace X] :
    ∃ (N : ℕ) (X' : Scheme.{u}) (i : X' ⟶ projectiveSpace A N) (π : X' ⟶ X) (U : X.Opens),
      IsClosedImmersion i ∧ i ≫ ProjSpace.toSpecBase A N = π ≫ (X ↘ Spec (.of A)) ∧
      genericPoint X ∈ U ∧ IsIso (π ∣_ U) := by
  obtain ⟨k, n, X', q, π, U, hq, hqπ, hU, hπ⟩ := exists_chow_multiProj (A := A) X
  refine ⟨ProjSpace.multiProjDim k n, X', q ≫ ProjSpace.multiProjEmb A k n, π, U,
    inferInstance, ?_, hU, hπ⟩
  rw [Category.assoc, ProjSpace.multiProjEmb_toSpecBase, hqπ]

theorem exists_chow {A : Type u} [CommRing A] [IsNoetherianRing A] (X : Scheme.{u})
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] [IrreducibleSpace X] :
    ∃ (N : ℕ) (X' : Scheme.{u}) (i : X' ⟶ projectiveSpace A N) (π : X' ⟶ X) (U : X.Opens),
      IsClosedImmersion i ∧ i ≫ ProjSpace.toSpecBase A N = π ≫ (X ↘ Spec (.of A)) ∧
      (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  obtain ⟨N, X', i, π, U, hi, hiπ, hU, hπ⟩ := exists_chow' (A := A) X
  exact ⟨N, X', i, π, U, hi, hiπ, ⟨_, hU⟩, hπ⟩

end

end GroundTheory.Arith.SchemeCoh
