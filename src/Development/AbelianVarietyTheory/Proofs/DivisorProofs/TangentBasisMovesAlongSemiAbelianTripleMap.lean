module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SabTan

theorem tanBasis_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ X) (x' : Sp T ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ i, IsTanAtG t x (v i)) → (∀ w, IsTanAtG t x w → ∃! cf : Fin n → S, IsCombAtG t x v cf w) → ∃ v' : Fin n → (Sp (DualNumber T) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = spMap (dualMap ψ) ≫ v i) ∧ (∀ i, IsTanAtG t' x' (v' i)) ∧ ∀ w, IsTanAtG t' x' w → ∃! cf : Fin n → T, IsCombAtG t' x' v' cf w := by
  intro E _ _ _ H X X' t t' j m S T _ _ ψ x x' hx n v hv hv'
  have := t.semi.comm
  have := t'.semi.comm
  obtain ⟨k₁, k₂⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange t ψ x n v hv hv'
  rw [← hx] at k₁ k₂
  have h₁ := isGrpPullback_pullback t'.G x'
  have hc := h₁.comp m.cart
  obtain ⟨a, b⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t (x' ≫ j) _ _ hc
  obtain ⟨-, b'⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t' x' _ _ h₁
  choose u hu using fun i => a _ (k₁ i)
  have hu' : ∀ i, (u i).left ≫ pullback.fst t'.G.hom x' ≫ m.φ = spMap (dualMap ψ) ≫ v i := hu
  have hb := (b n u).2 ⟨fun i => by rw [hu']; exact k₁ i, by rw [funext hu']; exact k₂⟩
  obtain ⟨c₁, c₂⟩ := (b' n u).1 hb
  exact ⟨fun i => (u i).left ≫ pullback.fst t'.G.hom x', fun i => by rw [Category.assoc]; exact hu' i, c₁, c₂⟩

end GlobalTheory.SabTan
