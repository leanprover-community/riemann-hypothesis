module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfGluingFacts
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem transported_frame_gram_orth : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (i j : Fin (D.sp.X 0).rank) (a : Fin D.R.rS), (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) = (D.sp.X 0).gram i j ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.eX a) = 0 ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.fY a) = 0 ∧ (VS D).hT (X.zu u) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) = 0 := by
  intro D X u F₀ tr i j a
  have key : ∀ (x y : (VS D).V), (VS D).hT (tr.wt.symm x) (tr.wt.symm y) = (VS D).hT x y := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have key2 : ∀ (x y : (VS D).V), (VS D).hT (tr.wt.symm x) y = (VS D).hT x (tr.wt y) := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply]
  have key3 : ∀ (x y : (VS D).V), (VS D).hT x (tr.wt.symm y) = (VS D).hT (tr.wt x) y := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key, Fin.cast_cast, Fin.cast_eq_self]
    exact D.sp.iXY_isom 0 hm _ _
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key2, tr.wt_e]
    exact (D.sp.hyp_orthX a _).1
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key2, tr.wt_f]
    exact (D.sp.hyp_orthX a _).2
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key3, tr.weight_z]
    exact Formalism.MainNotions.BridgeLemma₂.z_orth_embedding D u _

end GlobalTheory.Core.Mi
