module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

open scoped Classical

open NumberField GlobalTheory.CuspRep Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.WeightJoin

theorem main : PositivityTheory.Rg.BcB.F.RS.WeightJoin := by
  intro E _ _ _ hU n a b μ e π lam n₁ n₂ hn hμ hπ hw h₁ h₂ hinf τ lam' hτ
  obtain ⟨-, he, hc⟩ := GlobalTheory.BCT.MuProps.main E hU μ e hμ
  let U : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.TwistDisc.expo_pow]
  rcases NumberField.InfinitePlace.embedding_mk_eq τ with h | h
  · have hv := hw (InfinitePlace.mk τ)
    have hinfv := hinf (InfinitePlace.mk τ)
    have hev := he (InfinitePlace.mk τ)
    rw [h] at hv hinfv hev
    rw [GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, hev, ← hinfv]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ => by ring
  · have hv := GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn (hw (InfinitePlace.mk τ))
    have hinfv := hinf (InfinitePlace.mk τ)
    have hev := hc (InfinitePlace.mk τ)
    have hs₁ := (h₁ (InfinitePlace.mk τ).embedding).2
    have hs₂ := (h₂ (InfinitePlace.mk τ).embedding).2
    have hcc : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h]; exact star_star τ
    have hcc' : (starRingEnd ℂ).comp (InfinitePlace.mk τ).embedding = τ := hcc
    rw [hcc'] at hs₁ hs₂
    rw [hcc] at hv hev
    rw [GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, GlobalTheory.DefiniteBC.infOfWeight_dual, ← hinfv, hev, hs₁, hs₂,
      Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

end GlobalTheory.CompanionTheory.WeightJoin

end
