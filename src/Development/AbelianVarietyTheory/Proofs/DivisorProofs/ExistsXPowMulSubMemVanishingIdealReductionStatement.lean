module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsXPowMulSubMemVanishingIdealReduction
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_X_pow_mul_sub_mem_vanishingIdeal_reduction : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (β : X' ⟶ X) (q : X' ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback β q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ∀ (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull β)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s' : Fin (n + 1) → LB.Sec H'), H.IsLB → H'.IsLB → w.IsGen → (∀ j, Rel β w (s j) (s' j)) → VeryAmpleBy f H s → ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal (β ≫ f) s' → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ J) ∧ MvPolynomial.X i ^ N * F - G ∈ vanIdeal f s := by
  first | exact @GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal | exact GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal | (intros; apply GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal <;> assumption)
