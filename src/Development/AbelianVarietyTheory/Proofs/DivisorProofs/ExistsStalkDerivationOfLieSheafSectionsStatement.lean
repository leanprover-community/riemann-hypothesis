module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerivationOfLieSheafSections
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.exists_stalkDerivation_of_lieSheafSections : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)) (β : S.presheaf.stalk s →+* R) (n : ℕ) (V : S.Opens) (hs : s ∈ V) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), StalkData G s π ε m → ∃ δ : G.left.presheaf.stalk (unitSec G s) →+ R, (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) ∧ (∀ a, δ (π a) = 0) ∧ ∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V') (f : Γ(G.left, U)), δ (G.left.presheaf.germ U _ hU f) = ∑ i, w i * β (S.presheaf.germ V' s hs' (dualApp (τ i) hV (dUnit G he f))) := by
  first | exact @GlobalTheory.Nef.exists_stalkDer_of_lie | exact GlobalTheory.Nef.exists_stalkDer_of_lie | (intros; apply GlobalTheory.Nef.exists_stalkDer_of_lie <;> assumption)
