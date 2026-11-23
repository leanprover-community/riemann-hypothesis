module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulSectionsExactAlgClosedPolarisedAV
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory


theorem _root_.GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (c : x.P.A.left → x.P.L.ι), 1 ≤ n → x.P.g * n < l → FinZ x s → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ y, y ∈ x.P.L.U (c y)) → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p)) ∧ (∀ a : ∀ y : x.P.A.left, x.P.A.left.presheaf.stalk y, ∃ sg : RR x l, ∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) ∧ ∀ sg : RR x l, (∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) → ∃ ta : Fin x.P.g → RR x (l - 1 * n), ∀ c', (show Γ(x.P.A.left, x.P.L.U c') from sg.f c') = ∑ i, (show Γ(x.P.A.left, x.P.L.U c') from (s i).f c') * (show Γ(x.P.A.left, x.P.L.U c') from (ta i).f c') := by
  first | exact @GlobalTheory.koszul_sections_exact_field | exact GlobalTheory.koszul_sections_exact_field | (intros; apply GlobalTheory.koszul_sections_exact_field <;> assumption)
