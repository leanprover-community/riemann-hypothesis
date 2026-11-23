module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfSimilitudeIsoQuotientKernelInvariant
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.eq_of_similitudeIso_quotient_kernel_invariant : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → w.IsGen → w'.IsGen → (∀ v : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, (∀ r, v ≫ alMap x al r 1 = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → val w (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w' r z J = val w' (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w r z J) → ξ = ξ' := by
  first | exact @GlobalTheory.KeyKa.eq_of_similitude_invariant | exact GlobalTheory.KeyKa.eq_of_similitude_invariant | (intros; apply GlobalTheory.KeyKa.eq_of_similitude_invariant <;> assumption)
