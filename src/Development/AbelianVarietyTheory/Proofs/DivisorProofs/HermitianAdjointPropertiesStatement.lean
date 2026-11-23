module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointProperties
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

theorem _root_.GlobalTheory.T.hermitian_adjoint_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ (Y : Matrix (Fin r) (Fin r) E) (x y : Fin r → E), herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y)) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y * Z) = hAdj G Z * hAdj G Y) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y + Z) = hAdj G Y + hAdj G Z) ∧ (∀ (c : E) (Y : Matrix (Fin r) (Fin r) E), hAdj G (c • Y) = cc c • hAdj G Y) ∧ hAdj G 1 = 1 ∧ (∀ Y : Matrix (Fin r) (Fin r) E, hAdj G (hAdj G Y) = Y) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, (hAdj G Y).trace = cc Y.trace) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, IsSkew G Y ↔ hAdj G Y = -Y) := by
  first | exact @GlobalTheory.LieDisc.hAdj_algebra | exact GlobalTheory.LieDisc.hAdj_algebra | (intros; apply GlobalTheory.LieDisc.hAdj_algebra <;> assumption)
