module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GraphInversionEndomorphismCutBoundedDegree
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.graph_inversion_endomorphism_cut_bounded_degree : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (i : Option J), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p q : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (f : t.A ⟶ t.A), t.Shape Mat κ → f = i.elim (𝟙 t.A)⁻¹ t.act → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h) ∧ SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ n ^ j)).left (q h)) → CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2) := by
  first | exact @GlobalTheory.GraphCut.cutBy_graphIdeal | exact GlobalTheory.GraphCut.cutBy_graphIdeal | (intros; apply GlobalTheory.GraphCut.cutBy_graphIdeal <;> assumption)
