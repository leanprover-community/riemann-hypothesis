module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistSplitPlace

theorem isSplitPl_of_not_isConjPl (D : D7) (P : PlE D.host) (h : ¬ Formalism.IndefR.Lev.IsConjPl P P) : IsSplitPl D.host P := by
  unfold Formalism.IndefR.Lev.IsConjPl at h
  push Not at h
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, fun y hy hm => h y hm (hy.trans (GlobalTheory.DimPartsCompare.star_conj _).symm)⟩

theorem exists_splitPlace_of_mem_qPl : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.v = v ∧ s.w ∈ L.Q t := by
  rintro D T L μ0 hL i t v ⟨hg, w, hw, hn⟩
  have hu : (L.C.mu0 i).UnrAt w := (L.C.isMu0 i).unr w fun k hk => hg ⟨w, hw, k, hk⟩
  have hx : ¬ (L.xiH t).UnrAt w := fun h => hn fun x hx => by
    simpa [Host.HChar.loc] using congrArg₂ (· * ·) (hu x hx) (h x hx)
  have key : ∀ P ∈ L.Q t, NG.OverPl P v → ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.v = v ∧ s.w ∈ L.Q t := by
    intro P hP hov
    obtain ⟨s, hs⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D P
      (isSplitPl_of_not_isConjPl D P ((hL.Q_pl t P hP).2 P hP))
    refine ⟨s, HeightOneSpectrum.ext ?_, hs ▸ hP⟩
    rw [← s.w_under, hs]
    exact hov
  rcases (hL.Q_ram t w).1 hx with h | ⟨P, hP, hc⟩
  · exact key w h hw
  · refine key P hP ?_
    rw [GlobalTheory.DimPartsCompare.eq_cPl_of_isConjPl hc]
    exact (congrArg HeightOneSpectrum.asIdeal (GlobalTheory.DimPartsCompare.under_cPl w)).trans hw

end GlobalTheory.TwistSplitPlace
