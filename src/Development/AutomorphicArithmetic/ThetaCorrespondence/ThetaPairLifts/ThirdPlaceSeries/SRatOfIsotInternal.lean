module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RhoStabChiInLL0
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenspaceSpanOfIsotypicInternal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTheta
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsCAtState
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeAtState
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntCAtStateStatement
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite

@[expose] public section



section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
  GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genInjectivity false
set_option genSizeOfSpec false

namespace GlobalTheory.HeightCounting.RatSide
theorem sRat_of_isotInternal_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL := by
  intro hp hs hi hL
  have A := StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.formsC_at_state_alt hL) (StepW.and (_root_.GlobalTheory.HeightCounting.ThetaSt.main_alt_alt hL)
    (StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.HeckeAtState.heckeAtState_alt hL hp.decay hs.hkTr hs.hkRead)
    (StepW.and (_root_.GlobalTheory.T.intC_state_of_lvlPsi_stabC_heckeRd hL hp.decay hs.hkInt hs.hkTr hs.hkRead) (_root_.GlobalTheory.HeightCounting.RatSide.eigenspace_span_of_isotypicInternal_alt hp hi hL))))
  refine StepW.trans A (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx
  obtain ⟨hF, hθ, hH, hI, hE⟩ := H
  obtain ⟨θ, θne, hlp⟩ := hθ P x hx
  obtain ⟨hL', hst, h0, hrd⟩ := hH P x hx
  obtain ⟨eig, hea, hsp⟩ := hE P x hx θ hL' θne hlp hst h0 hrd
  have hint := hI P x hx θ hL' hlp hst hrd
  have hrc := GlobalTheory.Mem.RatDatRExp.rhoStab_chiInLL0 (Dof x) _ _ _ _ _ x.m.z.core x.m.z.R x.m.z.F x.m.z.cG x.m.z.geo (kKsOf x)
    (hkOf x) x.m.z.pins x.m.inGeo
  exact ⟨⟨kKsOf x, hkOf x,
    { Sb := SbD (Dof x)
      rho := fun j a b => (hrc j a b).1
      chi := fun j a b => (hrc j a b).2
      ks := fun j a b => (hF P x hx j a b).1
      fd := fun j a b => (hF P x hx j a b).2.1
      mk_fg := fun j a b => (hF P x hx j a b).2.2
      hL := hL'
      hs := hst
      hL_zero := h0
      θ := θ
      θ_ne := θne
      eig := eig
      span := hsp
      hL_int := hint },
    { hecke := hrd
      eig := hea
      Sb_le := overSet_SbD _
      lvl := hlp.1
      psi := hlp.2 }⟩⟩
theorem sRat_of_isotInternal_inputs : GlobalTheory.Published.DiscreteSeriesUpqUnique → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN →
    (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL :=
  fun _ => _root_.GlobalTheory.HeightCounting.RatSide.sRat_of_isotInternal_alt_alt
end GlobalTheory.HeightCounting.RatSide
end
end
end
