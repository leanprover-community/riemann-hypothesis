module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.LamExists

theorem re_mul_of_isReal {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (a : F) (x : Ainf F)
    (w : InfinitePlace F) : re (algebraMap F (Ainf F) a * x) w = re (algebraMap F (Ainf F) a) w * re x w := by
  have hr : (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w)).im = 0 := by
    rw [InfiniteAdeleRing.algebraMap_apply]
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have := InfinitePlace.isReal_iff.1 (hF.isReal w)
    exact Complex.conj_eq_iff_im.1 (RingHom.congr_fun this a)
  show (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w * x w)).re = _
  rw [map_mul, Complex.mul_re, hr, zero_mul, sub_zero]
  rfl

theorem re_ne_zero {F : Type} [Field F] [NumberField F] (a : F) (ha : a ≠ 0) (w : InfinitePlace F)
    (hF : IsTotallyReal F) : re (algebraMap F (Ainf F) a) w ≠ 0 := by
  have hr : (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w)).im = 0 := by
    rw [InfiniteAdeleRing.algebraMap_apply]
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have := InfinitePlace.isReal_iff.1 (hF.isReal w)
    exact Complex.conj_eq_iff_im.1 (RingHom.congr_fun this a)
  intro h0
  have : InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w) = 0 :=
    Complex.ext h0 hr
  rw [InfiniteAdeleRing.algebraMap_apply] at this
  rw [InfinitePlace.Completion.extensionEmbedding_coe, map_eq_zero] at this
  exact ha this

end GlobalTheory.SWQ.LamExists

theorem GlobalTheory.SWQ.exists_isLam : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ lam, IsLam ψ lam := by
  intro F _ _ hF ψ hψ
  haveI := hF
  obtain ⟨ψ₀, h₀⟩ := GlobalTheory.SnMass.Inhab.exists_isStdChar F
  obtain ⟨a, ha, h⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ₀ ψ h₀.1 hψ
  refine ⟨fun w => re (algebraMap F (Ainf F) a) w, fun w => GlobalTheory.SWQ.LamExists.re_ne_zero a ha w hF, fun x => ?_⟩
  rw [GlobalTheory.GaugeEx.CharLoc.psiInf_twist h, h₀.2.1]
  exact congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
    (Finset.sum_congr rfl fun w _ => GlobalTheory.SWQ.LamExists.re_mul_of_isReal hF a x w)
