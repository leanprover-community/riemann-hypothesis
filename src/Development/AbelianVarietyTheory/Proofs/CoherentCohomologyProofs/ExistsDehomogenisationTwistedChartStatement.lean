module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsGradedMapLinearCombination
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsDehomogenisationTwistedChart
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_dehomogenisation_twisted_chart : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (i : Fin (m + 1)) (r : Fin (m + 1) → Γ(Y, nonzeroLocus (s i))), (∀ j k, rs Y (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) = rs Y (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r j) * rs Y (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k)) → r i = 1 ∧ ∃ ε : GrSum (hx ⊤) →ₛₗ[MvPolynomial.eval₂Hom (cst f (nonzeroLocus (s i))) r] SecOn (tw M H 0) (nonzeroLocus (s i)), Function.Surjective ε ∧ (∀ n, ∀ y ∈ GrSum.grading (hx ⊤) n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • y = 0) ∧ ∀ a : SecOn (tw M H 0) ⊤, ε (GrSum.of (hx ⊤) 0 (SecOnR.of f _ ⊤ a)) = SecOn.restrict _ le_top a := by
  first | exact @GlobalTheory.AbLaw.exists_dehom_chart | exact GlobalTheory.AbLaw.exists_dehom_chart | (intros; apply GlobalTheory.AbLaw.exists_dehom_chart <;> assumption)
