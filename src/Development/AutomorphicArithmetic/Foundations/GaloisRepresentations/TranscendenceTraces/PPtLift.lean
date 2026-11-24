module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pt_map_ideal {Ω : Type} [Field Ω] {B : CommRingCat.{0}} (s : B ⟶ CommRingCat.of Ω) :
    (show PrimeSpectrum B from pt (Spec.map s)).asIdeal = RingHom.ker s.hom := by
  have h : (pt (Spec.map s) : Spec B) = PrimeSpectrum.comap s.hom (IsLocalRing.closedPoint Ω) := rfl
  change (pt (Spec.map s) : Spec B).asIdeal = _
  rw [h, RingHom.ker_eq_comap_bot]
  change Ideal.comap s.hom (IsLocalRing.maximalIdeal Ω) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]

private theorem exists_retract {Ω : Type} [Field Ω] [IsAlgClosed Ω] {B : CommRingCat.{0}} (φ : CommRingCat.of Ω ⟶ B)
    (hφ : φ.hom.IsIntegral) (q : Ideal B) [q.IsPrime] :
    ∃ s : B ⟶ CommRingCat.of Ω, φ ≫ s = 𝟙 _ ∧ RingHom.ker s.hom = q := by
  letI : Algebra Ω B := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral Ω B := ⟨hφ⟩
  have hb : Function.Bijective (algebraMap Ω (B ⧸ q)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : Ω ≃+* B ⧸ q := RingEquiv.ofBijective (algebraMap Ω (B ⧸ q)) hb
  refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp (Ideal.Quotient.mk q)), ?_, ?_⟩
  · ext a
    change e.symm (Ideal.Quotient.mk q (φ.hom a)) = a
    exact e.symm_apply_apply a
  · ext b
    change e.symm (Ideal.Quotient.mk q b) = 0 ↔ b ∈ q
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp

theorem UpperTheory.Gal.TranscendenceTraces.ptLift_of :
    PtLift := by
  intro V U r _ Ω _ _ x v hv
  obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := r) (g := x) v
    (IsLocalRing.closedPoint Ω) hv
  let P := pullback r x
  haveI : IsIntegralHom (pullback.snd r x) := inferInstance
  haveI : IsAffine P := isAffine_of_isAffineHom (pullback.snd r x)
  let φ : CommRingCat.of Ω ⟶ Γ(P, ⊤) := Spec.preimage (P.isoSpec.inv ≫ pullback.snd r x)
  have hφ' : Spec.map φ = P.isoSpec.inv ≫ pullback.snd r x := Spec.map_preimage _
  have hφ : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ']
    infer_instance
  let y : Spec Γ(P, ⊤) := P.isoSpec.hom t
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  obtain ⟨s, hs, hk⟩ := exists_retract φ hφ y.asIdeal
  refine ⟨Spec.map s ≫ P.isoSpec.inv ≫ pullback.fst r x, ?_, ?_⟩
  · have h1 : Spec.map s ≫ Spec.map φ = 𝟙 _ := by
      rw [← Spec.map_comp, hs, Spec.map_id]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv,
      ← hφ', ← Category.assoc, h1, Category.id_comp]
  · have hy : (pt (Spec.map s) : Spec Γ(P, ⊤)) = y :=
      PrimeSpectrum.ext ((pt_map_ideal s).trans hk)
    rw [← Category.assoc, pt_comp, pt_comp, hy]
    change (pullback.fst r x) (P.isoSpec.inv (P.isoSpec.hom t)) = v
    have h2 : P.isoSpec.inv (P.isoSpec.hom t) = t := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rw [h2, ht1]
