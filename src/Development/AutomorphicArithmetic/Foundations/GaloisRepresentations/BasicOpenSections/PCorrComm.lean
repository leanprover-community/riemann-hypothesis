module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvariance
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.corrComm :
    CorrComm := by
  intro l _ p Y S S' B B' O g s bS β hS i bS' γ hcomm hl T w c c' hc hc' k j
  obtain ⟨v, hv, hf, hb, hw⟩ := hc
  obtain ⟨v', hv', hf', hb', hw'⟩ := hc'
  have hsq : v' ≫ T.p = (c'.p ≫ i) ≫ s := by
    rw [Category.assoc]
    exact hv'.w
  obtain ⟨u, huv, hup⟩ : ∃ u, u ≫ v = v' ∧ u ≫ c.p = c'.p ≫ i :=
    ⟨hv.lift v' (c'.p ≫ i) hsq, hv.lift_fst _ _ _, hv.lift_snd _ _ _⟩
  subst huv
  have hpb : IsPullback u c'.p c.p i := IsPullback.of_right hv' hup hv
  have hfu : c'.f ≫ i = u ≫ c.f := by
    apply hS.hom_ext
    · simp only [Category.assoc]
      rw [hf', hf, Category.assoc]
    · calc (c'.f ≫ i) ≫ bS = (c'.f ≫ bS') ≫ γ := by rw [Category.assoc, hcomm, Category.assoc]
        _ = (c'.p ≫ bS') ≫ γ := by rw [hb']
        _ = c'.p ≫ i ≫ bS := by rw [Category.assoc, hcomm]
        _ = (u ≫ c.p) ≫ bS := by rw [hup, Category.assoc]
        _ = (u ≫ c.f) ≫ bS := by rw [Category.assoc, Category.assoc, hb]
  have hwu : c'.w = Wt.comap u c.w := by
    rw [hw', hw]
    funext Ω _ _ z
    simp only [Wt.comap, Category.assoc]
  exact TranscendenceTraces.corrBCQ_holds a8 l k j c' c i i u hpb hfu hwu hl
