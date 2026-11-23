module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixRelatingIntegralVectorZBases
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

theorem _root_.GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E), IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  first | exact @GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul | exact GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul | (intros; apply GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul <;> assumption)
