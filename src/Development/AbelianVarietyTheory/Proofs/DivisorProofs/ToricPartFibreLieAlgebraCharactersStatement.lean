module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPartFibreLieAlgebraCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.toric_part_fibre_lie_algebra_characters : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (E : TorusExtension ((Over.pullback x).obj G)), letI := E.addCommGroup; ∃ (ρ : O →+* Module.End ℤ E.X) (U : (E.X →+ k) → (epsPt x ⟶ G)), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk x ⟶ G).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ a l, U l ≫ act a = U (l.comp (ρ a).toAddMonoidHom) := by
  first | exact @GlobalTheory.torus_part_lie | exact GlobalTheory.torus_part_lie | (intros; apply GlobalTheory.torus_part_lie <;> assumption)
