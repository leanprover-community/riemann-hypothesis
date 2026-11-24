module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijectiveStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.coverOne_of :
    CoverOne := by
  intro R _ F G f V b h
  have hd : ∀ (V' W : Scheme.{0}) (g : V' ⟶ V) (k : W ⟶ V'),
      (∃ a : Sec F V', Sec.map f a = Sec.res g b) → ∃ a : Sec F W, Sec.map f a = Sec.res (k ≫ g) b := by
    rintro V' W g k ⟨a, ha⟩
    exact ⟨Sec.res k a, by rw [map_res, ha, res_res]⟩
  have h2 := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover V (fun W k => ∃ a : Sec F W, Sec.map f a = Sec.res k b) hd).1 h
  choose Wf k _ het hx a ha using h2
  obtain ⟨a', ha'⟩ := (GlobalTheory.T.sec_sigma_res_bijective R F Wf).2 a
  refine ⟨∐ Wf, Sigma.desc k, a', ?_, ?_, ?_⟩
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun i => het i
  · refine ⟨fun x => ?_⟩
    obtain ⟨y, hy⟩ := hx x
    refine ⟨Sigma.ι Wf x y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, hy]
  · refine (GlobalTheory.T.sec_sigma_res_bijective R G Wf).1 (funext fun i => ?_)
    show Sec.res (Sigma.ι Wf i) (Sec.map f a') = Sec.res (Sigma.ι Wf i) (Sec.res (Sigma.desc k) b)
    have e : Sec.res (Sigma.ι Wf i) a' = a i := congrFun ha' i
    rw [← map_res, e, ha, res_res, Sigma.ι_desc]
