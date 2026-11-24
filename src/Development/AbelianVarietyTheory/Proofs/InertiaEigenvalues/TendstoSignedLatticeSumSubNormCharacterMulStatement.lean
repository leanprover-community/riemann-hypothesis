module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumSubNormCharacterMul
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

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.tendsto_signedLatticeSum_sub_normCharacter_mul : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.LieReg → K.Small a → IsFrame B e π S → ∀ I ⊆ S, ∀ x : B.A, B.Plus x → Tendsto (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 - chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) atTop (𝓝 0) := by
  first | exact @GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible | exact GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible | (intros; apply GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible <;> assumption)
