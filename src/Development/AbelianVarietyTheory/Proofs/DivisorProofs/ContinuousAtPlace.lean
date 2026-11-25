module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
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

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacAny

variable {F : Type} [Field F] [NumberField F]

scoped instance invTwoV (v : HeightOneSpectrum (𝓞 F)) : Invertible (2 : Fv F v) :=
  invertibleOfNonzero (by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    exact (map_ne_zero _).2 two_ne_zero)

def psiV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (GlobalTheory.EmbChart.atPlace v).toAddMonoidHom

theorem psiV_apply (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    psiV ψ v t = ψ (GlobalTheory.EmbChart.atPlace v t) := rfl

theorem continuous_atPlace (v : HeightOneSpectrum (𝓞 F)) : Continuous (GlobalTheory.EmbChart.atPlace v) := by
  have h : (GlobalTheory.EmbChart.atPlace v : Fv F v → AF F) = fun t => (0, GlobalTheory.AdelicU.singleFin v t) := rfl
  rw [h]
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_psiV {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (psiV ψ v) :=
  hψ.comp (continuous_atPlace v)

section At

variable {v : HeightOneSpectrum (𝓞 F)}

local notation "ev" => GlobalTheory.AdelicU.evFin F v

end At

end GlobalTheory.VacAny
