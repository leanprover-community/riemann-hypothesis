module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendRegularThetaSectionAnyFractionField
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.extend_regularThetaSection_any_fractionField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R K) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R K) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R K) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R K (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R K)) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  first | exact @GlobalTheory.UMin.ExtFrac.ext_any_frac | exact GlobalTheory.UMin.ExtFrac.ext_any_frac | (intros; apply GlobalTheory.UMin.ExtFrac.ext_any_frac <;> assumption)
