module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MLabUnr
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabFixed
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
theorem labLP_twist_eq_labAt_ofDet : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (s : ℝ), D.naut.items₂ k (D.naut.plGw k v) (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (D.naut.plGw k v)) s) = _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) := by
  intro hPr hL D P S hT i k v hw hχ s
  haveI := host_isCMField D.host
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, (j : ℕ) + 1 = D.nd.j i := by
    have := D.nd.j_range i
    exact ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  have hμ : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) (S i _ hw).mu := hT.mu i _ hw j hj
  have hψ : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹ := by
    rw [P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv]
  have hc : IsComp (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 (D.naut.plGw k v)
      ((P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v)) := by
    rw [hψ]; exact ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩
  rw [P.lab k v, P.T.tw, WD.lab_lpTw, _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp hPr.fin hL D P _ _ _ hc, _root_.GlobalTheory.PendOf.localLabelPolynomial]
  have hηs : IsSmoothChar (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    have := ParLaws.isSmoothChar_loc (P.cf.eta⁻¹) (D.naut.plGw k v)
    convert this using 1
    exact MonoidHom.ext fun x => rfl
  have hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → (P.cf.eta.loc (D.naut.plGw k v))⁻¹ x = 1 := by
    intro x hx
    rw [MonoidHom.inv_apply, P.cf.isEta.unr _ x hx, inv_one]
  have e : (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v) =
      (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    rw [GlobalTheory.Published.ParamAboveModel.eq_loc hμ]
    rfl
  have key : ∀ (ξ' : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (h' : IsSmoothChar ξ'),
      ξ' = (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ →
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ' h')) =
        WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (S i _ hw).mu hχ)) := by
    rintro _ h' rfl
    exact _root_.GlobalTheory.LabFixed.lab_rcAt_ofDet_mul_eq hL D k v _ _ hχ hηs hu h'
  exact key _ _ e
end GlobalTheory.LabFixed
end
end
