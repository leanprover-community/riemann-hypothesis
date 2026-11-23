module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescendedTorsionIsometryThetaCoordinates
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.exists_descended_torsion_isometry_theta_coordinates : Laws → AllD fun {E} _ _ _ {H} D => ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (o : Full D K) (o' : Full D C), FullExt f o o' → ∀ (I' : FullI o') (ζ : ℕ → Kˣ), (∀ n, 0 < n → (I'.ζ n : C) = f (ζ n)) → ∃ I : FullI o, (∀ n, 0 < n → I.ζ n = ζ n) ∧ ∀ m, Odd m → (∀ (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Theta m v' → (withI o I).Theta m v) ∧ ∀ j, 0 < j → ∀ z (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Coord m (I'.ev j z) v' → (withI o I).Coord m (I.ev j z) v := by
  first | exact @GlobalTheory.DescendIso.exists_descend | exact GlobalTheory.DescendIso.exists_descend | (intros; apply GlobalTheory.DescendIso.exists_descend <;> assumption)
