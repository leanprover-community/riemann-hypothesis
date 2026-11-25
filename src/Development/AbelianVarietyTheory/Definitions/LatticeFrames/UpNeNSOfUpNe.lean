module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainNS

open GlobalTheory.ChainOnto

variable {D : D7}

def invFam (B : GlobalTheory.LFun.Fam D.host.E) : GlobalTheory.LFun.Fam D.host.E := fun w => (B w).map (·⁻¹)

def ParBoundInv (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (invFam B) s.V.rank ((s.V.rank : ℝ) / 2)

def ChainNS (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ S' : Finset (HeightOneSpectrum (𝓞 D.host.F)), c.S ⊆ S' →
  ∀ B : GlobalTheory.LFun.Fam D.host.E,
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) →
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))) (invFam B) D.R.r ((D.R.r : ℝ) / 2) →
    ∀ k < D.R.m, ∃ q ∉ S', Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q ∧
      GlobalTheory.Core.Rk.SW.NSAt (chainPar c B k) (c.chT (k + 1)) D.R.t q

end GlobalTheory.ChainNS

end
