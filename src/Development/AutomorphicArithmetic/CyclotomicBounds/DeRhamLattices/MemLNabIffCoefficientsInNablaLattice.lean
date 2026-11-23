module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.mem_lNab_iff_coefficients_in_nabla_lattice :
    ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (t : X.T),
      ∀ gramR c0R c0L, Bridge.FamTie X.R.B X.R.pl (X.R.Sb : Set (Pl D.host.E)) X.R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L →
      ∀ x, x ∈ lNab D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t ↔
        ∀ a, ∃ F : VV D.what₂.LL (lamV D j), F ∈ nabAtr (labLL D) (lamV D j) (Bridge.hLat (Vc D j) ((X.R.B.L j t).pres.y a)) ∧ (X.R.B.jL j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x)) ((X.R.B.L j t).pres.y a) = c0L j F := by
  intro D X j t gramR c0R c0L hT x
  obtain ⟨e, -, he, -, hN, -⟩ := hT.coefL j t
  have h1 : x ∈ lNab D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t ↔ ∀ a, (show (X.A3.A.MtCSD j t).Forms from GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x).1 a ∈ (X.A3.A.MtCSD j t).Nab a :=
    GlobalTheory.Mem.LiftForms.mem_lvlNab _ _ _ _ x
  refine h1.trans (forall_congr' fun a => ?_)
  generalize GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x = f
  have h2 : (X.R.B.jL j t f) ((X.R.B.L j t).pres.y a) = (X.R.B.L j t).pres.coef ((show (X.A3.A.MtCSD j t).Forms from f).1 a) :=
    GlobalTheory.PresBasic.ext_y (X.R.B.L j t).pres f a
  have h3 := hN a
  constructor
  · intro h
    refine ⟨e _, ?_, h2.trans (he _)⟩
    exact h3.le ⟨_, h, rfl⟩
  · rintro ⟨F, hF, hv⟩
    obtain ⟨v, hv1, hv2⟩ := h3.ge hF
    have h4 : (X.R.B.L j t).pres.coef ((show (X.A3.A.MtCSD j t).Forms from f).1 a) = (X.R.B.L j t).pres.coef v := by
      refine h2.symm.trans (hv.trans ?_)
      refine Eq.trans ?_ (he v).symm
      exact congrArg (c0L j) hv2.symm
    have h5 : (show (X.A3.A.MtCSD j t).Forms from f).1 a - v = 0 :=
      Bridge.ClassPres.coef_inj (X.R.B.L j t).pres (by rw [map_sub, h4, sub_self])
    rw [sub_eq_zero.1 h5]
    exact hv1
