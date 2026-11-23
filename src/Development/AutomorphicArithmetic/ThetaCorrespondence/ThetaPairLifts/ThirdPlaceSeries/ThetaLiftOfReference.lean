module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasThetaAtOfThetaMod
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtRows
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRowThetaModule
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.RefPair
theorem GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ X : RowMod D rep j, HasThetaAt D (M D.what₂.mu0 j h1 h2) X (cf.mu0 ⟨j - 1, by omega⟩) cf.eta := by
  intro hN hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters OverRows
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y hH hEx _ _ _ Rw a M tup Q hMA _ j h1 h2 => ?_
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  have hC : z.R.C = TC.cf w.I w.l Z := z.lev.C
  obtain ⟨X, hX⟩ := GlobalTheory.RefTheta.datum_real hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hH hEx M hMA i
  refine ⟨X, ?_⟩
  rw [← hC]
  exact hX
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.RefPair

theorem _root_.GlobalTheory.T.exists_theta_at_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ X : RowMod D rep j, HasThetaAt D (M D.what₂.mu0 j h1 h2) X (cf.mu0 ⟨j - 1, by omega⟩) cf.eta := by
  first | exact @_root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
