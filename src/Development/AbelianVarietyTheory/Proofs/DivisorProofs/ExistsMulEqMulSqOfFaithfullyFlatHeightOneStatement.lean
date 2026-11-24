module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqMulSqOfFaithfullyFlatHeightOne
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

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_mul_eq_mul_sq_of_faithfullyFlat_height_one : ∀ (O C : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CommRing C] [IsDomain C] [IsNoetherianRing C] [Algebra O C] [Module.FaithfullyFlat O C] (h : O), h ≠ 0 → (∃ (u : Cˣ) (g : C), algebraMap O C h = u * g ^ 2) → ∀ p : Ideal O, p.IsPrime → p.height = 1 → (Ideal.map (algebraMap O C) p).IsPrime → ∃ a b c : O, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2 := by
  first | exact @GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime | exact GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime | (intros; apply GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime <;> assumption)
