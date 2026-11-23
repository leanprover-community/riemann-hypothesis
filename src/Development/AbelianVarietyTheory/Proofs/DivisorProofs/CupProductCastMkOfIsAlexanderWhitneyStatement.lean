module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductCastMkOfIsAlexanderWhitney
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.cupProduct_cast_mk_of_isAlexanderWhitney : ∀ (q : ℕ) {S : Spc} (i : ℤ) (j : ℕ) (m : ℤ) (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (i - (j : ℤ)))) (m - 2 * (j : ℤ))) (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (j : ℤ))) (2 * (j : ℤ))) (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q i)) m), (twPairI q i (j : ℤ)).IsAW (sub_add_cancel m _) α.1 β.1 γ.1 → ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast (by ring) (by ring) : Ht q S m i) = CohomologyClass.mk γ := by
  first | (exact @GlobalTheory.PBFc.cup_cast_mk_of_isAW) | (exact GlobalTheory.PBFc.cup_cast_mk_of_isAW) | (intros; apply GlobalTheory.PBFc.cup_cast_mk_of_isAW  <;> assumption)
