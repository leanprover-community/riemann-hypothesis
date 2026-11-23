module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueSplitPrimeNotRootOfUnityStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCharQuotientLFunctionEntireNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.QuotVal

theorem val_quot_ne_one : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m → ∀ p : ℕ,
    GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    w.under (𝓞 D.host.F) ∉ c.S → GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w ≠ 1 := by
  intro D c hc i j hi hij hj p hp w hw hS h1
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  have hoff : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hS
  refine GlobalTheory.T.heckeChar_value_split_prime_not_root_of_unity D (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹)
    (GlobalTheory.Chain.isHeckeChar_div (QuotL.isHecke hc (by omega) (by omega)) (QuotL.isHecke hc (by omega) hj))
    (fun τ => ⟨_, ?_, GlobalTheory.Chain.hasInfExp_div (hc.exp ⟨i', by omega⟩ τ) (hc.exp ⟨j', by omega⟩ τ)⟩) p hp w hw
    ((hc.unr ⟨i', by omega⟩ w hoff).mul (hc.unr ⟨j', by omega⟩ w hoff).inv) ?_
  · have := QuotL.e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
      Fin.mk_lt_mk.2 (by omega))
    intro h0
    linarith
  · rw [h1]
    exact IsOfFinOrder.one

end GlobalTheory.ChainOnto.QuotVal

end
