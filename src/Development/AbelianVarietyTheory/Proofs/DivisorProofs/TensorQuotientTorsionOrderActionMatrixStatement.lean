module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientTorsionOrderActionMatrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorQuotientTorsion_orderAction_matrix : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (g : ℕ) (ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n), (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → ∀ n, 0 < n → ∀ (x : 𝓞 E) (a : Fin r → (Fin g → ℤ) × (Fin g → ℤ)) (p' q' : QkPt D'.toPre F n), PtRel T ν ν' p' (fun j => ev n (a j)) → PtRel T ν ν' q' (fun i => ev n (∑ j, ρ x i j • a j)) → (letI := H.starRing; QkAct o x p' q') := by
  first | exact @GlobalTheory.Mum.TensAct.qkAct_tens | exact GlobalTheory.Mum.TensAct.qkAct_tens | (intros; apply GlobalTheory.Mum.TensAct.qkAct_tens <;> assumption)
