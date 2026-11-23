module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairPowerSumValue
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

theorem _root_.GlobalTheory.T.eilenberg_zilber_homotopy_equivalence : ∀ (R : Type) [CommRing R] (X : SimplicialObject GlobalTheory.EtC.Spc), (∃ e : HomotopyEquiv (diagCx ((freeBi R).obj X)) (tot ((freeBi R).obj X)), ∀ n : ℕ, e.hom.f n = awF _ n) → ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X), ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n := by
  first | (exact @GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains) | (exact GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains) | (intros; apply GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains <;> assumption)
