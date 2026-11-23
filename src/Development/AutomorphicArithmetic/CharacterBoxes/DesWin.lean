module

public import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
public import Development.AutomorphicArithmetic.CharacterBoxes.DivinNOfHypV
public import Formalism.SharpRestriction.MuTuOfTuSize
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions

theorem topDesWin (𝒞 𝒞' ℰ : FamClass) (Cabs C0 eD eL : ℝ) (hEx : DesignExists (WithTw (WithSm 𝒞')) C0)
    (h1 : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm) (h2 : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → ℰ Fm)
    (hV : ∀ {eps : ℝ} (Fm : FamP eps), ℰ Fm → HypV Fm.toFamCore)
    (hN : Closed (Des 𝒞 C0) fun Fm _ => LinkN Fm)
    (hEta : Closed (Des 𝒞 C0) fun Fm _ => LinkEta Fm)
    (hIRR : Closed (Des 𝒞 C0) fun Fm _ => LinkIRR Fm)
    (hZ : Closed (Des 𝒞 C0) fun Fm _ => SmallLevelRankEq Fm)
    (hDIV : Closed (Des 𝒞 C0) fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm Cabs CH)
    (hRk : Closed (Des 𝒞 C0) fun Fm CH => ChosenE Fm C0 CH → NuFullF Fm ∧ J.MuRank Fm)
    (hG : Closed (Des 𝒞 C0) fun Fm _ => LinkG Fm)
    (hS : Closed (Des 𝒞 C0) fun Fm _ => TuSize Fm → LinkS Fm C0)
    (hGL : Closed (Des 𝒞 C0) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 eD eL) : FamilyClassConnected ℰ := by
  obtain ⟨ε1, hε1, hA⟩ := hN.and (hDIV.and (hEta.and (hIRR.and (hZ.and (hRk.and (hG.and (hS.and hGL)))))))
  obtain ⟨ε3, hε3, hEx⟩ := hEx
  refine ⟨eD, eL, min ε1 ε3, lt_min hε1 hε3, fun ε h0 hlt => ?_⟩
  obtain ⟨K, hK⟩ := hA ε h0 (le_of_lt (lt_of_lt_of_le hlt (min_le_left _ _)))
  obtain ⟨Fm, CH, hc, -, hL, hCh, hT, hDG⟩ := hEx ε h0 (le_of_lt (lt_of_lt_of_le hlt (min_le_right _ _))) K
  obtain ⟨aN, aD, aE, aI, aZ, aR, aG, aS, aGL⟩ := hK Fm CH ⟨⟨⟨h1 Fm hc.1.1, hc.1.2⟩, hc.2⟩, ⟨CH, hCh⟩, hT, hDG⟩ hL
  have hD := aD hT hDG aE (divinN_of_hypV Fm h0 (hV Fm (h2 Fm hc.1.1)) aN aZ)
  exact ⟨Fm, h2 Fm hc.1.1, aGL hT hDG hCh ⟨aG, aS hT, aI, hD,
    J.linkMu_of_linkDIV Fm hD (aR hCh).1 (aR hCh).2 (muTu_of_tuSize Fm h0 hT) (J.muDGam_of_fact Fm hDG)⟩⟩

end UpperTheory.Top

end
