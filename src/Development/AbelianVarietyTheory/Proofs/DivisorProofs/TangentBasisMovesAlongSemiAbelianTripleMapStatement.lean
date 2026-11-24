module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMovesAlongSemiAbelianTripleMap
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tangentBasis_moves_along_semiAbelianTripleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ X) (x' : Sp T ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ i, IsTanAtG t x (v i)) → (∀ w, IsTanAtG t x w → ∃! cf : Fin n → S, IsCombAtG t x v cf w) → ∃ v' : Fin n → (Sp (DualNumber T) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = spMap (dualMap ψ) ≫ v i) ∧ (∀ i, IsTanAtG t' x' (v' i)) ∧ ∀ w, IsTanAtG t' x' w → ∃! cf : Fin n → T, IsCombAtG t' x' v' cf w := by
  first | exact @GlobalTheory.SabTan.tanBasis_sabMap | exact GlobalTheory.SabTan.tanBasis_sabMap | (intros; apply GlobalTheory.SabTan.tanBasis_sabMap <;> assumption)
