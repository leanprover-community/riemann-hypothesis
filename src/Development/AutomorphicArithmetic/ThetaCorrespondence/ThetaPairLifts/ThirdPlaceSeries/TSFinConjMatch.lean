module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelConjugateCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.LinkLev
end GlobalTheory.Mem.R3.LinkLev
namespace GlobalTheory.Mem.R3.LinkLev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end GlobalTheory.Mem.R3.LinkLev
namespace GlobalTheory.Mem.R3.LinkLev
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3.Tr
end GlobalTheory.Mem.R3.LinkLev
namespace GlobalTheory.Mem.R3.LinkLev

theorem tS_fin_conj_match_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → w.y.y.tS ∈ Formalism.L2.Theta.GfC (Yc (q.w.D q.Z) 0) ∧ Formalism.IndefR.AutomorphicEvaluation.ConjLevel w.y.y.tS⁻¹ (levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (w.y.y.ιS ⁻¹' seeKS b.S.X) (fun k => seeChiS b.S.X (w.y.y.ιS k)) ∧ Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt w.x.R.toRealDat w.x.F.lv2 b.S.X w.y.y.instEq w.y.y.tS := by
  intro hL p
  refine GlobalTheory.Fc.EvP.of_all fun _ K _ => ?_
  intro q c b w hsc
  obtain ⟨sP, sS, hP, hS, hb⟩ := w.s
  have see := q.saturationAtWeightedPoint.see
  have ht : w.y.y.tS = q.saturationAtWeightedPoint.t := eq_of_heq w.pt.1
  have hι := (GlobalTheory.Mem.JIota.heq_iota_iff _ _ w.y.y.instEq w.y.y.ιS).1 w.y.y.ιS_eq
  have hX : b.S.X = q.saturationAtWeightedPoint.P.X := by
    rw [hb]
    exact spack_X_eq_of_heq (by rw [w.recPin.s.cols]; exact rfl) sP q.saturationAtWeightedPoint.P hP
  have key := levels_of_twArgs w.a w.x w.ax q.saturationAtWeightedPoint.P.X q.saturationAtWeightedPoint.P.inst q.saturationAtWeightedPoint.t ⟨see.conj, see.mat⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]
    exact see.fin
  · exact conjLevel_of_setting_eq _ _ hX _ _ _ hι _ _ ht _ _ key.1
  · exact of_setting_eq (fun X h t => Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt w.x.R.toRealDat w.x.F.lv2 X h t) _ _ hX _ _ _ _ ht key.2
end GlobalTheory.Mem.R3.LinkLev
end
