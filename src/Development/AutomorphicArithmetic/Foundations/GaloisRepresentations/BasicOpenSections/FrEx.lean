module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.frEx :
    FrEx := by
  intro p f hp κ kb _ _ _ hκ X t h τ hτ
  have K : absFrob (geom kb t) p f hp h ≫ pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) =
      pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ Spec.map (CommRingCat.ofHom (τ : kb →+* kb)) := by
    by_cases hk : (p : kb) = 0
    · have hk' : (p : Γ(Spec (CommRingCat.of kb), ⊤)) = 0 := by
        rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom p]
        erw [hk]
        exact map_zero _
      rw [GlobalTheory.SS.FrobField.absFrob_nat _ p f hp h hk']
      congr 1
      exact GlobalTheory.SS.FrobField.absFrob_spec kb p f hp hk' (τ : kb →+* kb) hτ
    · haveI : IsEmpty (geom kb t) := by
        refine ⟨fun x => hk ?_⟩
        have hinj := (((geom kb t).presheaf.germ ⊤ x trivial).hom.comp
          ((pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))).appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom)).injective
        apply hinj
        rw [map_zero]
        simp only [RingHom.comp_apply]
        rw [map_natCast, map_natCast, h, map_zero]
      exact isInitialOfIsEmpty.hom_ext _ _
  have hc : (absFrob (geom kb t) p f hp h ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) ≫ t =
      pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ Spec.map (CommRingCat.ofHom (algebraMap κ kb)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, K, Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    simp
  refine ⟨pullback.lift (absFrob (geom kb t) p f hp h ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))))
    (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) hc, pullback.lift_snd _ _ _, ?_, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, galMap_fst, pullback.lift_fst]
    · rw [Category.assoc, galMap_snd, ← Category.assoc, pullback.lift_snd, K]
  · intro Ω _ φ hφ x
    have hΩ := GlobalTheory.SS.FrobField.cast_zero_of_hom x h
    have e := GlobalTheory.SS.FrobField.absFrob_nat x p f hp hΩ h
    have e2 : absFrob (gp Ω) p f hp hΩ = Mod.sp φ := GlobalTheory.SS.FrobField.absFrob_spec Ω p f hp hΩ φ hφ
    rw [pullback.lift_fst, ← Category.assoc, ← e, e2, Category.assoc]
