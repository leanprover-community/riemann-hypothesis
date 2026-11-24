module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleTwistOfGeneratedAndVeryAmple
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
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.veryAmple_twist_of_generated_and_veryAmple : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H M : LB X) (n m : ℕ) (s : Fin (n + 1) → LB.Sec H) (u : Fin (m + 1) → LB.Sec M), H.IsLB → M.IsLB → VeryAmpleBy f H s → (⨆ a, nonzeroLocus (u a) = ⊤) → ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.tw M H 1)), VeryAmpleBy f (GlobalTheory.AbLaw.tw M H 1) s' := by
  first | exact @GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated | exact GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated | (intros; apply GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated <;> assumption)
