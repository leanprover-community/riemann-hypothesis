module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRangeRestrictEq
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RationalFormsAction

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem isTranslate_act_V (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (t : T0) (g : G)
    (x : (A.fam.L i t).S.Forms) :
    GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) ((R.HV i t).e (R.jV i t x))
      ((R.HV i t).e (R.jV i t ((A.fam.L i t).r g x))) := by

  have hred := hr i t
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate
  constructor
  ·
    obtain ⟨q, hq⟩ := (R.B.L i t).act_tie.red_surj g
    have hq' := hred q
    rw [hq] at hq'
    exact ⟨q, hq'.symm⟩
  · intro κ hκ h

    have hg : (R.B.L i t).act_tie.red κ = g := by
      apply R.eG.injective
      rw [hred κ]
      exact hκ

    have key := congrFun ((R.B.L i t).act_tie.act_eq g κ hg x) h
    have e1 := hj i t ((A.fam.L i t).r g x)
    have e2 := hj i t x

    refine (congrFun e1 h).trans (key.trans ?_)
    exact congrArg (fun w => ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ)⁻¹ : ℂˣ) : ℂ) • w)
      (congrFun e2 (h * (κ : Bridge.Gf (Vc D i)))).symm

end GlobalTheory.RationalFormsAction

theorem GlobalTheory.RationalFormsAction.act_eq_translate_lift_V : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_red_L → R.models_jV → ∀ i t (g : G) (x : (A.fam.L i t).S.Forms), ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ ∀ h, (R.HV i t).e (R.jV i t ((A.fam.L i t).r g x)) h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e (R.jV i t x) (h * (finHom _).rangeRestrict κ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hr hj i t g x

  have htr := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g x
  have hex := GlobalTheory.LiftEquivariance.exists_adelic_lift htr
  exact hex

end
