module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOutNeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutTranslate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HkMemFixed
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

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeAlg

theorem hk_alg : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by
  intro F _ _ _ _ ι _ _
  unfold HkAlg
  intro K e₁ e₂ h₁ h₂
  obtain ⟨hstar₁, hadj⟩ := GlobalTheory.CompanionTheory.HeckeAdj.hk_adjoint F ι K e₁ h₁
  refine ⟨GlobalTheory.CompanionTheory.HeckeMul.isHk_hconv h₁ h₂, hstar₁, ?_⟩
  intro V _ _ ρ v hv
  exact ⟨(GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e₁ h₁ V ρ v hv).1,
    GlobalTheory.CompanionTheory.HeckeMul.hk_hconv h₁ h₂ ρ hv,
    fun B hB w hw => hadj V ρ B hB v hv w hw⟩

end GlobalTheory.CompanionTheory.HeckeAlg
