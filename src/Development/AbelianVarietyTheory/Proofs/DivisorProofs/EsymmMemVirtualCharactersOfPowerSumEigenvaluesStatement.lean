module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.esymm_mem_virtualCharacters_of_powerSum_eigenvalues : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ) (x : G → Multiset ℂ), φ ∈ Virt ℂ ℂ G → (∀ (g : G) (j : ℕ), 0 < j → φ (g ^ j) = ((x g).map (· ^ j)).sum) → ∀ s : ℕ, (fun g => (x g).esymm s) ∈ Virt ℂ ℂ G := by
  first | exact @GlobalTheory.EsymmVirt.esymm_mem_virt | exact GlobalTheory.EsymmVirt.esymm_mem_virt | (intros; apply GlobalTheory.EsymmVirt.esymm_mem_virt <;> assumption)
