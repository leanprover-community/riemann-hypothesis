module

public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjEqOfPowEq
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.relIndex_map_conj_symm_of_relIndex_map_conj_pow_symm : ∀ (A : Type) [Group A] (K : Subgroup A) (g : A) (n : ℕ), 0 < n → (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 → K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0 → (K.map (MulAut.conj (g ^ n)).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj (g ^ n)).toMonoidHom) → (K.map (MulAut.conj g).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  first | exact @GlobalTheory.relIndex_conj_eq_of_pow_eq | exact GlobalTheory.relIndex_conj_eq_of_pow_eq | (intros; apply GlobalTheory.relIndex_conj_eq_of_pow_eq <;> assumption)
