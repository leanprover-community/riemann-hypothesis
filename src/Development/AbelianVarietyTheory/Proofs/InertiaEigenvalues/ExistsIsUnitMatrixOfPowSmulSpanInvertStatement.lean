module

public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitMatrixOfPowSmulSpanInvert
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.exists_isUnit_matrix_of_pow_smul_span_invert : ∀ (S EE W RW Y : Type) [CommRing S] [CommRing EE] [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW) (c : W →+* RW) (ψ : S →+* W) (Q : S), Function.Injective ι → (∀ s, ι (a s) = c (ψ s)) → IsUnit (a Q) → ∀ (q : ℕ) (x z : Fin q → Y), (∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) → (∀ j, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • z j = ∑ i, c (ψ (s i)) • x i) → (∀ i, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • x i = ∑ j, c (ψ (s j)) • z j) → ∃ A : Matrix (Fin q) (Fin q) EE, IsUnit A ∧ ∀ j, z j = ∑ i, ι (A i j) • x i := by
  first | exact @GlobalTheory.exists_isUnit_matrix_of_pow_smul_span | exact GlobalTheory.exists_isUnit_matrix_of_pow_smul_span | (intros; apply GlobalTheory.exists_isUnit_matrix_of_pow_smul_span <;> assumption)
