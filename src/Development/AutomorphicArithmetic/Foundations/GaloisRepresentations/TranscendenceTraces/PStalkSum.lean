module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_congr {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : R →ₛₗ[(e : R →+* S)] S :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a b => by simp [smul_eq_mul] }
  rw [Module.length, Module.length, WithBot.unbot_inj]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)

theorem UpperTheory.Gal.TranscendenceTraces.stalkSum_of :
    Chart → ArtSum → StalkSum := by
  intro hC hA V Ω _ _ r _
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC r Ω (𝟙 (gp Ω))
  have hv : IsIso v := hpb.isIso_fst_of_isIso
  have hr : r = inv v ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
    rw [IsIso.eq_inv_comp, hpb.w, Category.comp_id]
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) := by
    rw [Flat.SpecMap_iff]
    simpa [RingHom.flat_algebraMap_iff] using (inferInstance : Module.Flat Ω B)
  have hfi : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) := by
    rw [IsFinite.SpecMap_iff]
    simpa [RingHom.finite_algebraMap] using hfin
  have hR : Scheme.Hom.finrank r (IsLocalRing.closedPoint Ω) = Module.finrank Ω B := by
    rw [hr, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hs : ∀ P : PrimeSpectrum B, IsIso (v.stalkMap P) :=
    (IsOpenImmersion.iff_isIso_stalkMap (f := v)).mp inferInstance |>.2
  have e2 : ∀ P : PrimeSpectrum B,
      V.presheaf.stalk (v P) ≃+* Localization.AtPrime P.asIdeal := fun P =>
    ((asIso (v.stalkMap P)) ≪≫ Spec.stalkIso (CommRingCat.of B) P).commRingCatIsoToRingEquiv
  rw [hR, ← hA Ω B, ← finsum_comp_equiv v.homeomorph.toEquiv]
  refine finsum_congr fun P => ?_
  change (Module.length (V.presheaf.stalk (v P)) (V.presheaf.stalk (v P))).toNat = _
  rw [length_congr (e2 P)]
