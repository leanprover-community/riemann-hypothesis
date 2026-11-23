module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.CountT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefiniteRealisationChoice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem GlobalTheory.Top.link_alt_alt_bis : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hTF : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3)
    (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (sTy : Formalism.L2.SG.RowsPos.TypeP)
    (sNG : Formalism.L2.SG.RowsPos.RowNGP)
    (sM : Formalism.L2.SG.RowsPos.RowMainEqP)
    (sLp : Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩))
    (sO : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩)
    (h30 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (hInstR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank), Closed (D3 3 𝒜) fun Fm _ => TuSize Fm → LinkS Fm 3 := by
  intro 𝒜 sel selS hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have sRes : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.ResidEv Fm := Formalism.L2.SG.ResidEvFree.residEv_closed_free (D3 3 𝒜)
  let ssel : Formalism.L2.SG.ThmSOwn.SSel (D3 3 𝒜) :=
    fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩
  have lS := Formalism.L2.SG.ThmSOwn.theoremS_transport_link_zero (C0 := 3) (D3 3 𝒜) ssel hWu hRF
    (fun Fm hc x hx h i => (selS Fm (d3_a hc) x hx h i).locTied)
    (fun Fm hc x hx h i => Formalism.L2.SG.ThmSOwn.instTie_of_record (selS Fm (d3_a hc) x hx h i).inst
      (Formalism.MainNotions.RT.volTie_of_realTied _ ((sel Fm (d3_a hc)).2 x hx h i).T.theta.real) (hInstR Fm (d3_a hc) x hx h i).1
      (hInstR Fm (d3_a hc) x hx h i).2 (Fm.ties x i).cdScale_tie)
    (fun Fm hc x hx h i => Formalism.L2.SG.ThmSOwn.one_le_qqI_of_inst (selS Fm (d3_a hc) x hx h i).inst)
    hTF c30 (by linarith) hc30 sRes sTy sNG sM sLp sO h30
  exact lS
end
end
