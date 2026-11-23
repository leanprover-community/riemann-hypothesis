module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LlcSplit
theorem locV_unr_frobEig_of_hasSatake_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ → GlobalTheory.SmGL.HasSatake σ.ρ α → D.naut.unr (D.naut.locV i Q sp.w) ∧ D.naut.frobEig (D.naut.locV i Q sp.w) = Finset.univ.val.map (fun k => (((α k)⁻¹ : ℂˣ) : ℂ)) := by
  intro hL D P i Q sp σ α hS hα
  have h3 := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) sp σ hS
  rw [← P.H.emb i Q, ← D.nbc.embAV_loc i Q sp.w,
    _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 sp.w)) hα] at h3
  have hu : D.naut.unr (D.naut.locV i Q sp.w) :=
    (P.T.unr _ _).2 (by rw [h3]; exact (GlobalTheory.WeilDeligne.WD.unr_mk _).2 (GlobalTheory.WeilDeligne.WDRep.unr_diag _))
  refine ⟨hu, ?_⟩
  rw [P.T.frobEig _ _ hu, h3, GlobalTheory.WeilDeligne.WD.frobEig_diag]
end GlobalTheory.LlcSplit
end
