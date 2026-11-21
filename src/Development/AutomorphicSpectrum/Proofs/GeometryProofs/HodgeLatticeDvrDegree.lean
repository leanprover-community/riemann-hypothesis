import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransport
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenSecond
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsCurveInFibreDegree
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import Development.WeilBound.CoreStatements.HodgeTatePoints.FamilyEx
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitHermitianGeneratorsExist
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyHodgeLatticeData

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem HodgeLat.quot_det_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (u : Fin r → V × Module.Dual Ω V), (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) ∧ (detLat (𝓗.quot σ) u).IsVB 1 ⊤ ∧ ∀ (p : Cpt ξ) (A : Matrix (Fin r) (Fin r) Ω), (𝓗.quot σ).IsFrameAt (fun i => ∑ j, A i j • u j) p → (detLat (𝓗.quot σ) u).IsGenAt p A.det := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar r 𝓗 σ u hσ hu hspan
  have hvb : (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) := by
    intro p _
    obtain ⟨U, hpU, x, hx⟩ := 𝓗.free p
    refine ⟨U, hpU, fun i => HT.eigProj 𝓗.ρH σ (x i), HodgeDeterminantLattice.span_eigProj σ (hx p hpU), ?_⟩
    intro q _ hq
    refine ⟨HodgeDeterminantLattice.linearIndependent_eigProj σ (hx q hq), ?_⟩
    rw [HodgeLat.quot_apply]
    exact HodgeDeterminantLattice.eigQuot_eq_span σ (hx q hq) (fun a => ⟨⟨σ a, hσ q a⟩, rfl⟩)
  exact ⟨hvb, HodgeDeterminantLattice.detLat_isVB hvb hu hspan, fun p A hA => HodgeDeterminantLattice.detLat_of_frame hu hA⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_span_independent : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (u : Fin r → V × Module.Dual Ω V), (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) ∧ (detLat (𝓗.quot σ) u).IsVB 1 ⊤ ∧ ∀ (p : Cpt ξ) (A : Matrix (Fin r) (Fin r) Ω), (𝓗.quot σ).IsFrameAt (fun i => ∑ j, A i j • u j) p → (detLat (𝓗.quot σ) u).IsGenAt p A.det := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.quot_det_bundle
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.RegBase

theorem algebraMap_mem_regAt_of_base : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (s : X ⟶ Sp O), ξ ≫ s = spMap (algebraMap O Ω) → ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p := by
  intro X Ω _ ξ O _ _ s hs p o
  exact ⟨_, ConstReg.genMap_germ_const ξ s hs p o⟩

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.RegBase
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_constants_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (s : X ⟶ Sp O), ξ ≫ s = spMap (algebraMap O Ω) → ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.DegZ.RegBase.algebraMap_mem_regAt_of_base
end

section
section
open Polynomial NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem map_charpoly_lmul_eq_prod_embeddings (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [Fintype (E →+* Ω)]
    (hc : Nat.card (E →+* Ω) = Module.finrank ℚ E) (a : 𝓞 E) :
    (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom Ω) =
      ∏ s : E →+* Ω, (X - C (s (a : E))) := by
  classical
  let e := NumberField.RingOfIntegers.basis E
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* Ω) := by
    rw [← Module.finrank_eq_card_basis e, NumberField.RingOfIntegers.rank, ← hc,
      Nat.card_eq_fintype_card]
  let eqv := Fintype.equivOfCardEq hcard
  let P : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E →ₐ[ℤ] Ω :=
    fun j => ((eqv j).comp (algebraMap (𝓞 E) E)).toIntAlgHom
  have hP : Function.Injective P := by
    intro i j hij
    apply eqv.injective
    apply IsFractionRing.injective_comp_algebraMap (A := 𝓞 E) (K := E) (L := Ω)
    show (eqv i).comp (algebraMap (𝓞 E) E) = (eqv j).comp (algebraMap (𝓞 E) E)
    ext x
    exact DFunLike.congr_fun hij x
  have h := GlobalTheory.map_charpoly_leftMulMatrix_eq_prod_algHom e hP a
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, algebraMap_int_eq] at h
  refine h.trans ?_
  exact Fintype.prod_equiv eqv _ _ fun j => rfl

theorem charpoly_lmul_splits_of_conjugates (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [CharZero Ω] (O : Type) [CommRing O] [Algebra O Ω]
    (K : Type) [Field K] (g : O →+* K) (hinj : Function.Injective (algebraMap O Ω))
    (hc : Nat.card (E →+* Ω) = Module.finrank ℚ E)
    (hO : ∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) (a : 𝓞 E) :
    ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits := by
  classical
  haveI : Finite (E →+* Ω) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* Ω) := Fintype.ofFinite _
  have hO' : ∀ (s' : E →+* Ω) (a : 𝓞 E), ∃ y, algebraMap O Ω y = s' (a : E) :=
    fun s' a => RingHom.mem_range.mp (hO s' a)
  choose o ho using hO'
  have hΩ := GlobalTheory.CompanionTheory.Ar.Flat.DegZ.map_charpoly_lmul_eq_prod_embeddings E Ω hc a
  have hO2 : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom O) =
      ∏ s : E →+* Ω, (X - C (o s a)) := by
    apply Polynomial.map_injective (algebraMap O Ω) hinj
    rw [Polynomial.map_map,
      RingHom.ext_int ((algebraMap O Ω).comp (Int.castRingHom O)) (Int.castRingHom Ω), hΩ,
      Polynomial.map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ho]
  have hK : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K) =
      ∏ s : E →+* Ω, (X - C (g (o s a))) := by
    rw [RingHom.ext_int (Int.castRingHom K) (g.comp (Int.castRingHom O)), ← Polynomial.map_map, hO2,
      Polynomial.map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [hK]
  exact Polynomial.Splits.prod fun s _ => Polynomial.Splits.X_sub_C _

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_splits_of_embeddings : ∀ (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] [CharZero Ω] (O : Type) [CommRing O] [Algebra O Ω] (K : Type) [Field K] (g : O →+* K), Function.Injective (algebraMap O Ω) → Nat.card (E →+* Ω) = Module.finrank ℚ E → (∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) → ∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.DegZ.charpoly_lmul_splits_of_conjugates
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame

section Abstract

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {E : Type} [Field E] [NumberField E]
  {A : Subring K}

theorem mem_of_isFreeOn {ρ : 𝓞 E →+* Module.End K V} {L : Submodule A V} {N : ℕ} {t : Fin N → V}
    (h : HT.IsFreeOn ρ L t) (i : Fin N) : t i ∈ L := by
  have e : t i = ρ 1 (t i) := by simp
  rw [h.2.2, e, ← (RingOfIntegers.basis E).sum_repr 1, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_zsmul, LinearMap.smul_apply]
  exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _

theorem exists_lift_basis {R Y : Type} [CommRing R] [AddCommGroup Y] [Module R Y] (f : R →+* K)
    (hf : Function.Injective f) (hA : ∀ a, a ∈ A ↔ ∃ c, f c = a) (Φ : Y →+ V)
    (hsmul : ∀ (c : R) y, Φ (c • y) = f c • Φ y) (hinj : Function.Injective Φ)
    {ρ : 𝓞 E →+* Module.End K V} {L : Submodule A V} (hrange : ∀ v, v ∈ L ↔ ∃ y, Φ y = v)
    (rB : 𝓞 E → Y → Y) (hact : ∀ a y, Φ (rB a y) = ρ a (Φ y)) {N : ℕ} {t : Fin N → V}
    (h : HT.IsFreeOn ρ L t) :
    ∃ x : Fin N → Y, (∀ j, Φ (x j) = t j) ∧
      LinearIndependent R (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rB (RingOfIntegers.basis E q.2) (x q.1)) ∧
      Submodule.span R (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rB (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  choose x hx using fun i => (hrange (t i)).1 (mem_of_isFreeOn h i)
  have hΦ : ∀ c : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R,
      Φ (∑ q, c q • rB (RingOfIntegers.basis E q.2) (x q.1)) =
        ∑ q, f (c q) • ρ (RingOfIntegers.basis E q.2) (t q.1) := fun c => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hsmul, hact, hx]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc q
    have h1 := Fintype.linearIndependent_iff.1 h.1 (fun q => f (c q)) (by rw [← hΦ, hc, map_zero])
    exact hf ((h1 q).trans (map_zero f).symm)
  · rw [eq_top_iff]
    rintro y -
    have hy : Φ y ∈ L := (hrange _).2 ⟨y, rfl⟩
    rw [h.2.2] at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
    choose c' hc' using fun q => (hA (c q : K)).1 (c q).2
    have e : y = ∑ q, c' q • rB (RingOfIntegers.basis E q.2) (x q.1) := hinj (by
      rw [hΦ, ← hc]
      exact Finset.sum_congr rfl fun q _ => by rw [hc']; rfl)
    rw [e]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

end Abstract

theorem exists_of_mem_stdLat {Ω : Type} [Field Ω] {A : Subring Ω} {d : ℕ}
    {T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)} {w : (Fin d → Ω) × (Fin d → Ω)}
    (h : w ∈ stdLat A T) : ∃ y₀ : (Fin d → Ω) × (Fin d → Ω), (∀ i, y₀.1 i ∈ A ∧ y₀.2 i ∈ A) ∧ w = T y₀ := by
  induction h using Submodule.span_induction with
  | mem w hw => exact hw
  | zero => exact ⟨0, fun i => ⟨A.zero_mem, A.zero_mem⟩, (map_zero T).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, rfl⟩ := ha
    obtain ⟨z, hz, rfl⟩ := hb
    exact ⟨y + z, fun i => ⟨A.add_mem (hy i).1 (hz i).1, A.add_mem (hy i).2 (hz i).2⟩, (map_add T y z).symm⟩
  | smul c a _ ha =>
    obtain ⟨y, hy, rfl⟩ := ha
    exact ⟨(c : Ω) • y, fun i => ⟨A.mul_mem c.2 (hy i).1, A.mul_mem c.2 (hy i).2⟩, (map_smul T (c : Ω) y).symm⟩

theorem toVec_injective (Ω : Type) [Field Ω] (d : ℕ) : Function.Injective (toVec Ω d) := by
  intro y y' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 ((dotProductEquiv Ω (Fin d)).injective h2)

theorem toVec_surjective (Ω : Type) [Field Ω] (d : ℕ) : Function.Surjective (toVec Ω d) := by
  rintro ⟨a, φ⟩
  obtain ⟨b, rfl⟩ := (dotProductEquiv Ω (Fin d)).surjective φ
  exact ⟨(a, b), rfl⟩

section Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω] {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d r : ℕ}
  {M : LieModel t.G ξ (Fin d → Ω)} {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)}

theorem vmap_injective {R S : Type} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (vmap (d := d) f) := fun _ _ h =>
  Prod.ext (funext fun i => hf (congrFun (congrArg Prod.fst h) i))
    (funext fun i => hf (congrFun (congrArg Prod.snd h) i))

theorem toH_injective (hξ : IsCptGen ξ) (S : GermSys t ξ M) (p : Cpt ξ) : Function.Injective (toH S p) :=
  fun _ _ h => vmap_injective (hξ.inj p)
    ((GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.1.1 (toVec_injective Ω d h))

theorem toH_mem_iff (S : GermSys t ξ M) {𝓗 : HodgeLat M.lat ρ H.bar r} (hG : S.Gives 𝓗) (p : Cpt ξ)
    (v : (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) : v ∈ 𝓗.HL p ↔ ∃ y, toH S p y = v := by
  constructor
  · intro hv
    obtain ⟨w, rfl⟩ := toVec_surjective Ω d v
    obtain ⟨y₀, hy₀, rfl⟩ := exists_of_mem_stdLat ((hG.2 p w).1 hv)
    choose a ha using fun i => (hy₀ i).1
    choose b hb using fun i => (hy₀ i).2
    refine ⟨(a, b), ?_⟩
    have e : vmap (genMap ξ p) (a, b) = y₀ := Prod.ext (funext ha) (funext hb)
    rw [toH, e]
  · rintro ⟨y, rfl⟩
    exact (hG.2 p _).2 (Submodule.subset_span ⟨vmap (genMap ξ p) y,
      fun i => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩)

theorem toH_rhoH (S : GermSys t ξ M) {𝓗 : HodgeLat M.lat ρ H.bar r} (hG : S.Gives 𝓗) (p : Cpt ξ) (a : 𝓞 E)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (rhoH (S.g p).B a y) = 𝓗.ρH a (toH S p y) := by
  have h1 := vmap_rhoH (S.mapK p) a y
  have h2 := LinearMap.congr_fun ((GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.2.2.1 a) (vmap (genMap ξ p) y)
  have h3 := hG.1 a (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))
  have e1 := congrArg (fun z => toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) z)) h1
  have e2 := congrArg (toVec Ω d) h2.symm
  exact (e1.trans e2).trans h3.symm

end Germ

theorem exists_basis_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (σ : E →+* Ω) (u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)), IsCptGen ξ → S.Gives 𝓗 → (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → ∀ p : Cpt ξ, ∃ (x : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) (A : Matrix (Fin r) (Fin r) Ω), IsHBasis (S.g p).B x ∧ (𝓗.quot σ).IsFrameAt (fun j => ∑ l, A j l • u l) p ∧ ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (x j)) = ∑ l, A j l • u l := by
  intro E _ _ _ H _ X t Ω _ _ ξ d r M S ρ 𝓗 σ u hξ hG hσ _ hu p
  obtain ⟨U, hU, x, hx⟩ := 𝓗.free p
  have hfree := hx p hU
  obtain ⟨x', h1, h2, h3⟩ := exists_lift_basis (genMap ξ p) (hξ.inj p) (A := regAt ξ p) (fun _ => Iff.rfl)
    (AddMonoidHom.mk' (toH S p) (toH_add S p)) (toH_smul S p) (toH_injective hξ S p)
    (toH_mem_iff S hG p) (fun a y => rhoH (S.g p).B a y) (toH_rhoH S hG p) hfree
  have hA : ∀ i, ∃ c : Fin r → Ω, ∑ l, c l • u l = HT.eigProj 𝓗.ρH σ (x i) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hu ▸ HT.LatBasic.eigProj_mem _ _ _)
  choose A hA using hA
  refine ⟨x', Matrix.of A, ⟨h2, h3⟩, ?_, fun j => ?_⟩
  · have e : (fun j => ∑ l, Matrix.of A j l • u l) = fun j => HT.eigProj 𝓗.ρH σ (x j) := funext hA
    rw [e]
    exact ⟨HodgeDeterminantLattice.linearIndependent_eigProj σ hfree,
      HodgeDeterminantLattice.eigQuot_eq_span σ hfree fun a => ⟨⟨_, hσ p a⟩, rfl⟩⟩
  · have := h1 j
    change toH S p (x' j) = x j at this
    rw [this]
    exact (hA j).symm

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_germ_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (σ : E →+* Ω) (u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)), IsCptGen ξ → S.Gives 𝓗 → (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → ∀ p : Cpt ξ, ∃ (x : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) (A : Matrix (Fin r) (Fin r) Ω), IsHBasis (S.g p).B x ∧ (𝓗.quot σ).IsFrameAt (fun j => ∑ l, A j l • u l) p ∧ ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (x j)) = ∑ l, A j l • u l := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.IsoMap

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}

def Zp {n : ℕ} (a : Pt R n d) : Prop := ∀ i, constantCoeff (a i) = 0

theorem zp_pt {n : ℕ} (j : Fin n) : Zp (pt R d j) := fun i => by
  show constantCoeff (X (j, i) : PS R n d) = 0
  simp

theorem zp_zero {n : ℕ} : Zp (0 : Pt R n d) := fun i => by simp

theorem zp_comp1 {n : ℕ} {φ : Pt R 1 d} {a : Pt R n d} (hφ : Zp φ) (ha : Zp a) : Zp (comp1 φ a) :=
  fun i => constantCoeff_ev (CZ.cons ha CZ.nil) (hφ i)

theorem zp_mP {n : ℕ} {a : Pt R n d} (ha : Zp a) : Zp (mP f a) := fun i => by
  have h : coeff (0 : Fin n × Fin d →₀ ℕ) (MvPowerSeries.map f (a i)) = f (coeff 0 (a i)) := coeff_map _ _ _
  rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, ha i, map_zero] at h
  exact h

theorem map_ev1 {n : ℕ} {a : Pt R n d} (ha : Zp a) (g : PS R 1 d) :
    MvPowerSeries.map f (ev ![a] g) = ev ![mP f a] (MvPowerSeries.map f g) := by
  rw [map_ev' f (CZ.cons ha CZ.nil), mV_cons, mV_nil]

theorem map_ev2 {n : ℕ} {a b : Pt R n d} (ha : Zp a) (hb : Zp b) (g : PS R 2 d) :
    MvPowerSeries.map f (ev ![a, b] g) = ev ![mP f a, mP f b] (MvPowerSeries.map f g) := by
  rw [map_ev' f (CZ.cons ha (CZ.cons hb CZ.nil)), mV_cons, mV_cons, mV_nil]

theorem map_ev3 {n : ℕ} {a b c : Pt R n d} (ha : Zp a) (hb : Zp b) (hc : Zp c) (g : PS R 3 d) :
    MvPowerSeries.map f (ev ![a, b, c] g) = ev ![mP f a, mP f b, mP f c] (MvPowerSeries.map f g) := by
  rw [map_ev' f (CZ.cons ha (CZ.cons hb (CZ.cons hc CZ.nil))), mV_cons, mV_cons, mV_cons, mV_nil]

theorem mapPoint_comp1' {n : ℕ} (φ : Pt R 1 d) {a : Pt R n d} (ha : Zp a) :
    mP f (comp1 φ a) = comp1 (mP f φ) (mP f a) := by
  funext i
  exact map_ev1 f ha (φ i)

variable {O : Type} [CommRing O] [StarRing O]

theorem zp_add (B : Germ.FB R d O) {n : ℕ} {a b : Pt R n d} (ha : Zp a) (hb : Zp b) : Zp (B.G.add a b) :=
  fun i => constantCoeff_ev (CZ.cons ha (CZ.cons hb CZ.nil)) (B.G.const i)

theorem zp_act (B : Germ.FB R d O) (a : O) : Zp (B.A.act a) := B.A.const a

variable {f} {B : Germ.FB R d O} {C : Germ.FB S d O}

theorem mapPoint_add (h : IsMapOf f B C) {n : ℕ} {a b : Pt R n d} (ha : Zp a) (hb : Zp b) :
    mP f (B.G.add a b) = C.G.add (mP f a) (mP f b) := by
  funext i
  show MvPowerSeries.map f (ev ![a, b] (B.G.F i)) = ev ![mP f a, mP f b] (C.G.F i)
  rw [h.F, map_ev2 f ha hb]

theorem mapPoint_act (h : IsMapOf f B C) (a : O) : mP f (B.A.act a) = C.A.act a := by
  funext i
  exact (h.act a i).symm

theorem isIso_mP {B₂ : Germ.FB R d O} {C₂ : Germ.FB S d O} {φ ψ : Germ.Pt R 1 d} {lam : Germ.PS R 2 d}
    (h₁ : IsMapOf f B C) (h₂ : IsMapOf f B₂ C₂) (I : IsIso B B₂ φ ψ lam) :
    IsIso C C₂ (mP f φ) (mP f ψ) (MvPowerSeries.map f lam) := by
  have hφ : Zp φ := I.c₁
  have hψ : Zp ψ := I.c₂
  refine ⟨zp_mP f hφ, zp_mP f hψ, ?_, ?_, ⟨?_, ?_⟩, ?_, fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
  · have h := congrArg (mP f) I.inv₁
    rwa [mapPoint_comp1' f _ hψ, mapPoint_pt] at h
  · have h := congrArg (mP f) I.inv₂
    rwa [mapPoint_comp1' f _ hφ, mapPoint_pt] at h
  · have h := congrArg (MvPowerSeries.map f) I.ax.1
    simpa only [map_ev2 f zp_zero (zp_pt 0), mapPoint_zero f, mapPoint_pt, map_one] using h
  · have h := congrArg (MvPowerSeries.map f) I.ax.2
    simpa only [map_ev2 f (zp_pt 0) zp_zero, mapPoint_zero f, mapPoint_pt, map_one] using h
  · have h := congrArg (mP f) I.law
    simp only [mapPoint_comp1' f _ (zp_add _ (zp_pt _) (zp_pt _)), mapPoint_comp1' f _ (zp_pt _),
      mapPoint_add h₁ (zp_comp1 hφ (zp_pt _)) (zp_comp1 hφ (zp_pt _)), mapPoint_add h₂ (zp_pt _) (zp_pt _), mapPoint_pt] at h
    simpa only [mapPoint_comp1' f _ (zp_pt _), mapPoint_pt] using h
  · have h := congrArg (mP f) (I.act a)
    rwa [mapPoint_comp1' f _ (zp_act _ _), mapPoint_comp1' f _ hφ, mapPoint_act h₁, mapPoint_act h₂] at h
  · have h := congrArg (MvPowerSeries.map f) I.ph1
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, map_ev3 f, mapPoint_comp1' f, mapPoint_add h₂, mapPoint_pt,
      ← h₁.ph1, ← h₂.ph1, hφ, zp_pt, zp_comp1, zp_add] at h
    exact h
  · have h := congrArg (MvPowerSeries.map f) I.ph2
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, map_ev3 f, mapPoint_comp1' f, mapPoint_add h₂, mapPoint_pt,
      ← h₁.ph2, ← h₂.ph2, hφ, zp_pt, zp_comp1, zp_add] at h
    exact h
  · have h := congrArg (MvPowerSeries.map f) I.sy
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, mapPoint_comp1' f, mapPoint_pt,
      ← h₁.sy, ← h₂.sy, hφ, zp_pt, zp_comp1] at h
    exact h
  · have h := congrArg (MvPowerSeries.map f) (I.ad a)
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, mapPoint_comp1' f, mapPoint_act h₂, mapPoint_pt,
      ← h₁.ad, ← h₂.ad, hφ, zp_pt, zp_comp1, zp_act] at h
    exact h

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.IsoMap

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem isIso_map : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (B B₂ : Germ.FB R d O) (C C₂ : Germ.FB S d O) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d),
    IsMapOf f B C → IsMapOf f B₂ C₂ → IsIso B B₂ φ ψ lam →
      IsIso C C₂ (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i)) (MvPowerSeries.map f lam) := by
  intro R S _ _ f d O _ _ B B₂ C C₂ φ ψ lam h₁ h₂ I
  exact IsoMap.isIso_mP h₁ h₂ I

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_first : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B B₂ : Germ.FB R d O) (C C₂ : Germ.FB S d O) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d), IsMapOf f B C → IsMapOf f B₂ C₂ → IsIso B B₂ φ ψ lam → IsIso C C₂ (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i)) (MvPowerSeries.map f lam) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isIso_map
end

section
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fibreCurve_curveIn_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) :=
  @PositivityTheory.Xgn.exists_curve_in_fibre_degree

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_curve_degree_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.fibre_power_free_conj_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p := by
  first | exact @PositivityTheory.HtPt.Cf.fib_inj | exact PositivityTheory.HtPt.Cf.fib_inj
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_power_free_conj_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.fibre_power_free_conj_injective
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.GermFam

theorem isMapOf_cancel {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {d : ℕ} {O : Type} [CommRing O]
    [StarRing O] {f : R →+* R₁} {g : R₁ →+* R₂} {B : Germ.FB R d O} {B₁ : Germ.FB R₁ d O} {B₂ : Germ.FB R₂ d O}
    (h : IsMapOf f B B₁) (h' : IsMapOf (g.comp f) B B₂) : IsMapOf g B₁ B₂ where
  F := fun i => by rw [h'.F, h.F, MvPowerSeries.map_comp]; rfl
  act := fun a i => by rw [h'.act, h.act, MvPowerSeries.map_comp]; rfl
  ph1 := by rw [h'.ph1, h.ph1, MvPowerSeries.map_comp]; rfl
  ph2 := by rw [h'.ph2, h.ph2, MvPowerSeries.map_comp]; rfl
  sy := by rw [h'.sy, h.sy, MvPowerSeries.map_comp]; rfl
  ad := fun a => by rw [h'.ad, h.ad, MvPowerSeries.map_comp]; rfl

section Lat

variable {Ω : Type} [Field Ω] {A : Subring Ω} {d : ℕ}

theorem mem_stdLat {T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)}
    {x : (Fin d → Ω) × (Fin d → Ω)} (hx : x ∈ stdLat A T) :
    ∃ y : (Fin d → Ω) × (Fin d → Ω), (∀ i, y.1 i ∈ A ∧ y.2 i ∈ A) ∧ x = T y := by
  unfold stdLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, fun i => ⟨A.zero_mem, A.zero_mem⟩, (map_zero T).symm⟩
  | add x x' _ _ h h' =>
    obtain ⟨y, hy, rfl⟩ := h
    obtain ⟨y', hy', rfl⟩ := h'
    exact ⟨y + y', fun i => ⟨A.add_mem (hy i).1 (hy' i).1, A.add_mem (hy i).2 (hy' i).2⟩, (map_add T y y').symm⟩
  | smul c x _ h =>
    obtain ⟨y, hy, rfl⟩ := h
    refine ⟨(c : Ω) • y, fun i => ⟨A.mul_mem c.2 (hy i).1, A.mul_mem c.2 (hy i).2⟩, ?_⟩
    rw [map_smul]
    rfl

theorem trans_integral {T₀ T T' : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)}
    (he : T = T₀ ∘ₗ T') (h0 : Function.Injective T₀) (hl : stdLat A T₀ = stdLat A T)
    (y : (Fin d → Ω) × (Fin d → Ω)) (hy : ∀ i, y.1 i ∈ A ∧ y.2 i ∈ A) :
    ∀ i, (T' y).1 i ∈ A ∧ (T' y).2 i ∈ A := by
  have h1 : T y ∈ stdLat A T := Submodule.subset_span ⟨y, hy, rfl⟩
  rw [← hl] at h1
  obtain ⟨y₁, hy₁, e⟩ := mem_stdLat h1
  have h2 : T' y = y₁ := h0 (by rw [← e, he]; rfl)
  rwa [h2]

theorem entries_mem (φ ψ : Germ.Pt Ω 1 d) (lam : Germ.PS Ω 2 d) (hψφ : lin ψ 1 * lin φ 1 = 1)
    (h : ∀ y : (Fin d → Ω) × (Fin d → Ω), (∀ i, y.1 i ∈ A ∧ y.2 i ∈ A) →
      ∀ i, (transH φ ψ lam y).1 i ∈ A ∧ (transH φ ψ lam y).2 i ∈ A) (a b : Fin d) :
    lin φ 1 a b ∈ A ∧ lin ψ 1 a b ∈ A ∧ bil lam 1 1 a b ∈ A := by
  classical
  have hs : ∀ (l : Fin d) (i : Fin d), (Pi.single l 1 : Fin d → Ω) i ∈ A := fun l i => by
    by_cases e : i = l
    · subst e; simpa using A.one_mem
    · simpa [Pi.single_apply, e] using A.zero_mem
  have h1 : ∀ a b, lin φ 1 a b ∈ A := fun a b => by
    have := (h (Pi.single b 1, 0) (fun i => ⟨hs b i, A.zero_mem⟩) a).1
    simpa [transH_apply] using this
  have h2 : ∀ a b, lin ψ 1 a b ∈ A := fun a b => by
    have := (h (0, Pi.single a 1) (fun i => ⟨A.zero_mem, hs a i⟩) b).2
    simpa [transH_apply] using this
  have h3 : ∀ a b, ((lin ψ 1).transpose * (bil lam 1 1).transpose) a b ∈ A := fun a b => by
    have h0 := (h (Pi.single b 1, 0) (fun i => ⟨hs b i, A.zero_mem⟩) a).2
    have e : (transH φ ψ lam (Pi.single b 1, 0)).2 a =
        ((lin ψ 1).transpose * (bil lam 1 1).transpose) a b := by
      simp [transH_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rwa [e] at h0
  have h4 : (bil lam 1 1).transpose =
      (lin φ 1).transpose * ((lin ψ 1).transpose * (bil lam 1 1).transpose) := by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hψφ, Matrix.transpose_one, Matrix.one_mul]
  refine ⟨h1 a b, h2 a b, ?_⟩
  have h5 : bil lam 1 1 a b = (bil lam 1 1).transpose b a := rfl
  rw [h5, h4, Matrix.mul_apply]
  exact A.sum_mem fun c _ => A.mul_mem (h1 c b) (h3 c a)

end Lat

section Curve

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ϖ : Ω}

theorem stalk_sq (Γ : FibreCurve ξ ϖ) (i : Γ.C.I) :
    (Γ.C.v i).valuationSubring.subtype.comp (Scheme.stalkClosedPointTo (Γ.z i)).hom =
      (Scheme.stalkClosedPointTo Γ.η).hom.comp (X.presheaf.stalkSpecializes (Γ.generic_centre_specializes i)).hom := by
  have key := ProjectiveLinePlaces.stalk_square (Γ.generic_centre_specializes i) (Scheme.stalkClosedPointTo (Γ.z i))
    (Scheme.stalkClosedPointTo Γ.η) (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype)
    ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk Γ.η).trans ((Γ.z_gen i).symm.trans
      (congrArg (Spec.map (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype) ≫ ·)
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (Γ.z i))).symm))
  exact (congrArg CommRingCat.Hom.hom key).symm

theorem val_le_one (hξ : IsCptGen ξ) (Γ : FibreCurve ξ ϖ) (i : Γ.C.I) (a : X.presheaf.stalk (centre Γ.η))
    (ha : genMap ξ ⟨centre Γ.η, Γ.η_spec⟩ a ∈ regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩) :
    Γ.C.v i ((Scheme.stalkClosedPointTo Γ.η).hom a) ≤ 1 := by
  obtain ⟨c, hc⟩ := ha
  have h1 : (X.presheaf.stalkSpecializes (Γ.generic_centre_specializes i)).hom c = a :=
    hξ.inj ⟨centre Γ.η, Γ.η_spec⟩
      ((ProjectiveLinePlaces.genMap_specializes (Γ.generic_centre_specializes i) Γ.η_spec (Γ.z_spec i) c).trans hc)
  have h2 : ((Scheme.stalkClosedPointTo (Γ.z i)).hom c : Γ.κ) = (Scheme.stalkClosedPointTo Γ.η).hom
      ((X.presheaf.stalkSpecializes (Γ.generic_centre_specializes i)).hom c) := DFunLike.congr_fun (stalk_sq Γ i) c
  rw [h1] at h2
  rw [← h2]
  exact ((Scheme.stalkClosedPointTo (Γ.z i)).hom c).2

end Curve

section Point

variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R]

theorem natCast_residueField (z : Sp R ⟶ X) (p : ℕ) (hp : (p : R) = 0) :
    (p : X.residueField (centre z)) = 0 := by
  have hnu : ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (centre z)) := fun h => by
    have h1 := h.map (Scheme.stalkClosedPointTo z).hom
    have e : (Scheme.stalkClosedPointTo z).hom (p : X.presheaf.stalk (centre z)) = (0 : R) :=
      (map_natCast (Scheme.stalkClosedPointTo z).hom p).trans hp
    exact not_isUnit_zero (M₀ := R) ((congrArg IsUnit e).mp h1)
  have h2 := (IsLocalRing.residue_eq_zero_iff _).2 hnu
  rw [map_natCast] at h2
  exact h2

theorem centre_spMap {S : Type} [CommRing S] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (z : Sp R ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom f) ≫ z) = centre z := by
  change z ((Spec.map (CommRingCat.ofHom f)) (IsLocalRing.closedPoint S)) = z (IsLocalRing.closedPoint R)
  congr 1
  exact IsLocalRing.comap_closedPoint f

end Point

section Main

theorem exists_residue_germ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]
    (hbar : ∀ a : 𝓞 E, star a = H.bar a) (X : Scheme.{0}) (t : SAB H X) (hpow : PowFns t)
    {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X) (d : ℕ) (g : GermAt t x d) (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) (hf : FibPF t (centre x)) :
    ∃ Bk : Germ.FB (IsLocalRing.ResidueField R) d (𝓞 E), IsMapOf (IsLocalRing.residue R) g.B Bk ∧ ConjInj Bk p := by
  obtain ⟨g₂, hm, -⟩ := GlobalTheory.T.formal_germ_base_change E H hbar X t R (IsLocalRing.ResidueField R) (IsLocalRing.residue R) x d g
  haveI : CharP (IsLocalRing.ResidueField R) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast (IsLocalRing.residue R), hp, map_zero])
  refine ⟨g₂.B, hm, GlobalTheory.T.fibre_power_free_conj_injective E H hbar X t hpow _ p _ d g₂ ?_⟩
  have e := centre_spMap (IsLocalRing.residue R) x
  change FibPF t (centre (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ x))
  rw [e]
  exact hf

end Main

section Integral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X : Scheme.{0}}
  {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}

theorem integral_at (S : GermSys t ξ M) {ϖ : Ω} (Γ : FibreCurve ξ ϖ) (hξ : IsCptGen ξ) (i : Γ.C.I)
    {B' : Germ.FB (X.presheaf.stalk (centre Γ.η)) d (𝓞 E)} {φ' ψ' : Germ.Pt (X.presheaf.stalk (centre Γ.η)) 1 d}
    {lam' : Germ.PS (X.presheaf.stalk (centre Γ.η)) 2 d}
    (hiso : IsIso (S.g ⟨centre Γ.η, Γ.η_spec⟩).B B' φ' ψ' lam')
    (he : transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩)
        (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩) =
      transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩) ∘ₗ
        transH (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (φ' l))
          (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (ψ' l))
          (MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) lam'))
    (hl : stdLat (regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩)
        (transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩)) =
      stdLat (regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩)
        (transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩)
          (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩)))
    (a b : Fin d) :
    Γ.C.v i (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l)) 1 a b) ≤ 1 ∧
      Γ.C.v i (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l)) 1 a b) ≤ 1 ∧
      Γ.C.v i (bil (MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam') 1 1 a b) ≤ 1 := by
  have h0 := (GlobalTheory.T.formal_isomorphism_transport Ω d (𝓞 E) S.g₀.B (S.BK ⟨centre Γ.η, Γ.η_spec⟩) _ _ _
    (S.iso ⟨centre Γ.η, Γ.η_spec⟩)).2.2.1.1
  have h1 := (GlobalTheory.T.formal_isomorphism_transport _ d (𝓞 E) _ _ _ _ _ hiso).2.1
  have h2 : lin (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (ψ' l)) 1 *
      lin (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (φ' l)) 1 = 1 := by
    rw [lin_map, lin_map, ← Matrix.map_mul]
    exact (congrArg (fun m => Matrix.map m (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩)) h1).trans
      (Matrix.map_one _ (map_zero _) (map_one _))
  obtain ⟨e1, e2, e3⟩ := entries_mem (A := regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩) _ _ _ h2
    (fun y hy => trans_integral he h0 hl y hy) a b
  rw [lin_map, Matrix.map_apply] at e1 e2
  rw [bil_map, Matrix.map_apply] at e3
  refine ⟨?_, ?_, ?_⟩
  · have e : (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l)) 1 a b : Γ.κ) =
        (Scheme.stalkClosedPointTo Γ.η).hom (lin φ' 1 a b) :=
      congrFun (congrFun (lin_map (Scheme.stalkClosedPointTo Γ.η).hom φ' 1) a) b
    rw [e]
    exact val_le_one hξ Γ i _ e1
  · have e : (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l)) 1 a b : Γ.κ) =
        (Scheme.stalkClosedPointTo Γ.η).hom (lin ψ' 1 a b) :=
      congrFun (congrFun (lin_map (Scheme.stalkClosedPointTo Γ.η).hom ψ' 1) a) b
    rw [e]
    exact val_le_one hξ Γ i _ e2
  · have e : (bil (MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam') 1 1 a b : Γ.κ) =
        (Scheme.stalkClosedPointTo Γ.η).hom (bil lam' 1 1 a b) :=
      congrFun (congrFun (bil_map (Scheme.stalkClosedPointTo Γ.η).hom lam' 1 1) a) b
    rw [e]
    exact val_le_one hξ Γ i _ e3

end Integral

theorem germ_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (O : Type) [CommRing O] (s : X ⟶ Sp O) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (p : ℕ) [Fact p.Prime] (Γ : FibreCurve ξ ϖ) [CharP Γ.κ p], IsCptGen ξ → PowFns t → (∀ q : Cpt ξ, (p : X.residueField q.1) = 0 → FibPF t q.1) → ∃ F : Family Γ.C p d (𝓞 E), IsMapOf (Scheme.stalkClosedPointTo Γ.η).hom (S.g ⟨centre Γ.η, Γ.η_spec⟩).B F.B ∧ ∀ i, IsMapOf (Scheme.stalkClosedPointTo (Γ.z i)).hom (S.g ⟨centre (Γ.z i), Γ.z_spec i⟩).B (F.Bi i) ∧ ∃ (φ' ψ' : Germ.Pt (X.presheaf.stalk (centre Γ.η)) 1 d) (lam' : Germ.PS (X.presheaf.stalk (centre Γ.η)) 2 d), transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩) = transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩) ∘ₗ transH (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (φ' l)) (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (ψ' l)) (MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) lam') ∧ F.φ i = (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l)) ∧ F.ψ i = (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l)) ∧ F.lam i = MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam' := by
  intro E _ _ _ H _ hbar X t Ω _ ξ d M S O _ s _ _ ϖ p _ Γ _ hξ hpow hfib
  have hκ : ((p : ℕ) : Γ.κ) = 0 := CharP.cast_eq_zero Γ.κ p
  obtain ⟨g0, m0, -⟩ := GlobalTheory.T.formal_germ_base_change E H hbar X t _ _ (Scheme.stalkClosedPointTo Γ.η).hom
    (X.fromSpecStalk (centre Γ.η)) d (S.g ⟨centre Γ.η, Γ.η_spec⟩)
  have place : ∀ i : Γ.C.I, ∃ (Bi : Germ.FB (Γ.C.v i).valuationSubring d (𝓞 E)) (BK : Germ.FB Γ.κ d (𝓞 E))
      (Bk : Germ.FB (IsLocalRing.ResidueField (Γ.C.v i).valuationSubring) d (𝓞 E))
      (φ' ψ' : Germ.Pt (X.presheaf.stalk (centre Γ.η)) 1 d) (lam' : Germ.PS (X.presheaf.stalk (centre Γ.η)) 2 d),
      IsMapOf (Scheme.stalkClosedPointTo (Γ.z i)).hom (S.g ⟨centre (Γ.z i), Γ.z_spec i⟩).B Bi ∧
      IsMapOf (Γ.C.v i).valuationSubring.subtype Bi BK ∧ IsMapOf (IsLocalRing.residue _) Bi Bk ∧ ConjInj Bk p ∧
      IsIso g0.B BK (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l))
        (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l))
        (MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam') ∧
      transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩)
          (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩) =
        transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩) ∘ₗ
          transH (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (φ' l))
            (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (ψ' l))
            (MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) lam') ∧
      (stdLat (regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩)
          (transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩)) =
        stdLat (regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩)
          (transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩)
            (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩)) → ∀ a b,
        Γ.C.v i (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l)) 1 a b) ≤ 1 ∧
        Γ.C.v i (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l)) 1 a b) ≤ 1 ∧
        Γ.C.v i (bil (MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam') 1 1 a b) ≤ 1) := by
    intro i
    obtain ⟨gi, mi, -⟩ := GlobalTheory.T.formal_germ_base_change E H hbar X t _ (Γ.C.v i).valuationSubring
      (Scheme.stalkClosedPointTo (Γ.z i)).hom (X.fromSpecStalk (centre (Γ.z i))) d
      (S.g ⟨centre (Γ.z i), Γ.z_spec i⟩)
    obtain ⟨gK, mK, -⟩ := GlobalTheory.T.formal_germ_base_change E H hbar X t _ Γ.κ (Γ.C.v i).valuationSubring.subtype _ d gi
    have hp : ((p : ℕ) : (Γ.C.v i).valuationSubring) = 0 := Subtype.ext (by simpa using hκ)
    have ex : spMap (Scheme.stalkClosedPointTo (Γ.z i)).hom ≫ X.fromSpecStalk (centre (Γ.z i)) = Γ.z i :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk (Γ.z i)
    have hf : FibPF t (centre (Γ.z i)) :=
      hfib ⟨_, Γ.z_spec i⟩ (natCast_residueField (Γ.z i) p hp)
    obtain ⟨Bk, mk, hk⟩ := exists_residue_germ E H hbar X t hpow _ d gi p hp (by rw [ex]; exact hf)
    obtain ⟨B', φ', ψ', lam', hm', hiso, he⟩ := S.gen ⟨centre (Γ.z i), Γ.z_spec i⟩ ⟨centre Γ.η, Γ.η_spec⟩
      (Γ.generic_centre_specializes i)
    have hK : IsMapOf (Scheme.stalkClosedPointTo Γ.η).hom B' gK.B :=
      isMapOf_cancel hm' (by rw [← stalk_sq Γ i]; exact mi.trans mK)
    exact ⟨gi.B, gK.B, Bk, φ', ψ', lam', mi, mK, mk, hk,
      GlobalTheory.T.intersection_first _ _ _ d _ _ _ _ _ _ _ _ m0 hK hiso, he, fun hl a b => integral_at S Γ hξ i hiso he hl a b⟩
  choose Bi BK Bk φ' ψ' lam' mi mK mk hk hiso he hint using place
  obtain ⟨Y, hY, -⟩ := GlobalTheory.T.fibre_curve_degree_compare X Ω ξ O s ϖ Γ hξ
  obtain ⟨U, hU, hloc⟩ := S.loc ⟨centre Γ.η, Γ.η_spec⟩
  have hfin := Y.ae U hU
  rw [hY] at hfin
  exact ⟨{ B := g0.B, Bi := Bi, BK := BK, Bk := Bk, mapK := mK, mapk := mk, inj := hk
           φ := fun i l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' i l)
           ψ := fun i l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' i l)
           lam := fun i => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (lam' i)
           iso := hiso
           ae := hfin.subset fun i hi h => hi (hint i (hloc ⟨_, Γ.z_spec i⟩ h)) }, m0,
    fun i => ⟨mi i, φ' i, ψ' i, lam' i, he i, rfl, rfl, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.GermFam
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_curve_germ_powers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (O : Type) [CommRing O] (s : X ⟶ Sp O) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (p : ℕ) [Fact p.Prime] (Γ : FibreCurve ξ ϖ) [CharP Γ.κ p], IsCptGen ξ → PowFns t → (∀ q : Cpt ξ, (p : X.residueField q.1) = 0 → FibPF t q.1) → ∃ F : Family Γ.C p d (𝓞 E), IsMapOf (Scheme.stalkClosedPointTo Γ.η).hom (S.g ⟨centre Γ.η, Γ.η_spec⟩).B F.B ∧ ∀ i, IsMapOf (Scheme.stalkClosedPointTo (Γ.z i)).hom (S.g ⟨centre (Γ.z i), Γ.z_spec i⟩).B (F.Bi i) ∧ ∃ (φ' ψ' : Germ.Pt (X.presheaf.stalk (centre Γ.η)) 1 d) (lam' : Germ.PS (X.presheaf.stalk (centre Γ.η)) 2 d), transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩) = transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩) ∘ₗ transH (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (φ' l)) (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (ψ' l)) (MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) lam') ∧ F.φ i = (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l)) ∧ F.ψ i = (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l)) ∧ F.lam i = MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.DegZ.GermFam.germ_family
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegProd

open Module

section Alg

variable {O : Type} [CommRing O] {J : Type} [Fintype J] (b : Basis J ℤ O)
  {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  (ρ : O →+* Module.End K V) (χ : O →+* K)

abbrev eigSpan : Submodule K V := ⨆ a : O, LinearMap.range (ρ a - χ a • LinearMap.id)

theorem exists_quot_basis {r : ℕ} (x : Fin r → V)
    (hli : LinearIndependent K fun q : Fin r × J => ρ (b q.2) (x q.1))
    (hsp : Submodule.span K (Set.range fun q : Fin r × J => ρ (b q.2) (x q.1)) = ⊤) :
    ∃ bq : Basis (Fin r) K (V ⧸ eigSpan ρ χ), (∀ j, bq j = (eigSpan ρ χ).mkQ (x j)) ∧
      ∀ (c : Fin r × J → K) (j : Fin r),
        bq.repr ((eigSpan ρ χ).mkQ (∑ q, c q • ρ (b q.2) (x q.1))) j = ∑ k, c (j, k) * χ (b k) := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Basis (Fin r × J) K V, ∀ q, B q = ρ (b q.2) (x q.1) :=
    ⟨Basis.mk hli hsp.ge, fun q => by simp⟩
  obtain ⟨φ, hφB⟩ : ∃ φ : V →ₗ[K] (Fin r → K),
      ∀ q, φ (B q) = χ (b q.2) • Pi.single q.1 (1 : K) :=
    ⟨B.constr K fun q => χ (b q.2) • Pi.single q.1 (1 : K), fun q => B.constr_basis K _ q⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Fin r → K) →ₗ[K] V ⧸ eigSpan ρ χ,
      ∀ j, ψ (Pi.single j 1) = (eigSpan ρ χ).mkQ (x j) :=
    ⟨(Pi.basisFun K (Fin r)).constr K fun j => (eigSpan ρ χ).mkQ (x j), fun j => by
      simpa using (Pi.basisFun K (Fin r)).constr_basis K (fun j => (eigSpan ρ χ).mkQ (x j)) j⟩
  have hχ : ∀ a : O, χ a = ∑ k, ((b.repr a k : ℤ) : K) * χ (b k) := by
    intro a
    conv_lhs => rw [← b.sum_repr a]
    simp [map_sum, zsmul_eq_mul]
  have hρ : ∀ (a : O) (v : V), ρ a v = ∑ k, (b.repr a k : ℤ) • ρ (b k) v := by
    intro a v
    conv_lhs => rw [← b.sum_repr a]
    simp [map_sum, LinearMap.sum_apply]
  have hφx : ∀ (a : O) (j : Fin r), φ (ρ a (x j)) = χ a • Pi.single j (1 : K) := by
    intro a j
    rw [hρ, map_sum, hχ a, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := hφB (j, k)
    rw [hB] at h
    rw [map_zsmul, h, mul_smul, Int.cast_smul_eq_zsmul]
  have hx : ∀ j, φ (x j) = Pi.single j (1 : K) := by
    intro j
    simpa using hφx 1 j
  have hφρ : ∀ (a : O) (v : V), φ (ρ a v) = χ a • φ v := by
    intro a v
    have h : φ ∘ₗ ρ a = χ a • φ := by
      refine B.ext fun q => ?_
      rw [LinearMap.comp_apply, LinearMap.smul_apply, hφB, hB, ← Module.End.mul_apply, ← map_mul,
        hφx, map_mul, mul_smul]
    exact LinearMap.congr_fun h v
  have hWk : eigSpan ρ χ ≤ LinearMap.ker φ := by
    refine iSup_le fun a => ?_
    rintro _ ⟨v, rfl⟩
    simp [hφρ]
  have hmk : ∀ v, (eigSpan ρ χ).mkQ v = ψ (φ v) := by
    have h : (eigSpan ρ χ).mkQ = ψ ∘ₗ φ := by
      refine B.ext fun q => ?_
      rw [LinearMap.comp_apply, hφB, map_smul, hψ, hB, ← map_smul, Submodule.mkQ_apply,
        Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact Submodule.mem_iSup_of_mem (b q.2) (LinearMap.mem_range.2 ⟨x q.1, rfl⟩)
    exact fun v => LinearMap.congr_fun h v
  let e : (V ⧸ eigSpan ρ χ) ≃ₗ[K] (Fin r → K) :=
    LinearEquiv.ofLinear ((eigSpan ρ χ).liftQ φ hWk) ψ
      ((Pi.basisFun K (Fin r)).ext fun j => by simp [hψ, hx])
      (Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
        exact (hmk v).symm))
  have he : ∀ v, e ((eigSpan ρ χ).mkQ v) = φ v := fun v => by simp [e]
  refine ⟨(Pi.basisFun K (Fin r)).map e.symm, fun j => ?_, fun c j => ?_⟩
  · simp [e, hψ]
  · rw [Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, he, Pi.basisFun_repr]
    simp_rw [← hB]
    rw [map_sum, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single j]
    · simp [hφB]
    · intro j' _ hj'
      simp [hφB, Pi.single_apply, Ne.symm hj']
    · simp

theorem isLatOf_quot {C : ACurve K} (i : C.I) {r : ℕ} {x : Fin r → V}
    (bq : Basis (Fin r) K (V ⧸ eigSpan ρ χ)) (L : AddSubgroup V) (hχ : ∀ a, C.v i (χ a) ≤ 1)
    (hbq : ∀ (c : Fin r × J → K) (j : Fin r),
      bq.repr ((eigSpan ρ χ).mkQ (∑ q, c q • ρ (b q.2) (x q.1))) j = ∑ k, c (j, k) * χ (b k))
    (hL : ∀ y, y ∈ L ↔ ∃ c : Fin r × J → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • ρ (b q.2) (x q.1)) :
    IsLatOf C i bq (L.map (eigSpan ρ χ).mkQ.toAddMonoidHom) := by
  classical
  delta GlobalTheory.CompanionTheory.Ar.Crv.IsLatOf
  intro w
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (hL y).1 hy
    intro j
    show C.v i (bq.repr ((eigSpan ρ χ).mkQ (∑ q, c q • ρ (b q.2) (x q.1))) j) ≤ 1
    rw [hbq c j]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    exact mul_le_one' (hc (j, k)) (hχ (b k))
  · intro hw
    have h1 : χ 1 = ∑ k, ((b.repr 1 k : ℤ) : K) * χ (b k) := by
      conv_lhs => rw [← b.sum_repr 1]
      simp [map_sum, zsmul_eq_mul]
    refine ⟨∑ q : Fin r × J, (((b.repr 1 q.2 : ℤ) : K) * bq.repr w q.1) • ρ (b q.2) (x q.1),
      (hL _).2 ⟨fun q : Fin r × J => ((b.repr 1 q.2 : ℤ) : K) * bq.repr w q.1, fun q => ?_, rfl⟩, ?_⟩
    · show C.v i (((b.repr 1 q.2 : ℤ) : K) * bq.repr w q.1) ≤ 1
      rw [map_mul]
      refine mul_le_one' ?_ (hw q.1)
      have h := hχ ((b.repr 1 q.2 : ℤ) : O)
      rwa [map_intCast] at h
    · show (eigSpan ρ χ).mkQ _ = w
      refine bq.repr.injective (Finsupp.ext fun j => ?_)
      rw [hbq (fun q : Fin r × J => ((b.repr 1 q.2 : ℤ) : K) * bq.repr w q.1) j]
      calc ∑ k, ((b.repr 1 k : ℤ) : K) * bq.repr w j * χ (b k)
          = bq.repr w j * ∑ k, ((b.repr 1 k : ℤ) : K) * χ (b k) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ = bq.repr w j := by rw [← h1, map_one, _root_.mul_one]

end Alg

section Place

variable {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] {K : Type} [Field K] {C : ACurve K}
  {p d r : ℕ} (F : Family C p d (𝓞 E)) (i : C.I)

private theorem rhoH_vmap_of_isMapOf {R R₂ : Type} [CommRing R] [CommRing R₂] {n : ℕ} {O : Type} [CommRing O]
    [StarRing O] (f : R →+* R₂) {B : Germ.FB R n O} {B₂ : Germ.FB R₂ n O} (h : IsMapOf f B B₂) (a : O)
    (u : (Fin n → R) × (Fin n → R)) : rhoH B₂ a (vmap f u) = vmap f (rhoH B a u) := by
  have hrho : ∀ a : O, rho B₂ a = (rho B a).map f := by
    intro a
    ext k l
    delta GlobalTheory.CompanionTheory.Ar.Conj.rho GlobalTheory.CompanionTheory.Ar.Conj.lin
    simp only [h.act, MvPowerSeries.coeff_map]
    rfl
  have hbil : bil (B₂.ad a) 1 1 = (bil (B.ad a) 1 1).map f := by
    ext k l
    delta GlobalTheory.CompanionTheory.Ar.Conj.bil
    simp only [h.ad, MvPowerSeries.coeff_map]
    rfl
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · delta GlobalTheory.CompanionTheory.Ar.Conj.rhoH GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap
    simp [hrho, RingHom.map_mulVec, Matrix.toLin'_apply, Function.comp_def]
  · delta GlobalTheory.CompanionTheory.Ar.Conj.rhoH GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap
    simp [hrho, hbil, RingHom.map_mulVec, Matrix.toLin'_apply, Matrix.transpose_map,
      Function.comp_def]

theorem rhoH_trans (a : 𝓞 E)
    (u : (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring)) :
    rhoH F.B a (transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype u)) =
      transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (rhoH (F.Bi i) a u)) := by
  have h := (GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (F.iso i)).2.2.2.2.1 a
  rw [← LinearMap.comp_apply, h, LinearMap.comp_apply, rhoH_vmap_of_isMapOf _ (F.mapK i)]

private theorem exists_injective_linearMap_eq_vmap {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ) :
    ∃ L : ((Fin n → A) × (Fin n → A)) →ₗ[A] ((Fin n → Ω) × (Fin n → Ω)),
      Function.Injective L ∧ ∀ u, L u = vmap A.subtype u := by
  refine ⟨⟨⟨vmap A.subtype, ?_⟩, ?_⟩, ?_, fun u => rfl⟩
  · intro u u'
    exact Prod.ext (funext fun k => by delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap; simp)
      (funext fun k => by delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap; simp)
  · intro s u
    exact Prod.ext (funext fun k => by delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap; simp [Algebra.smul_def])
      (funext fun k => by delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap; simp [Algebra.smul_def])
  intro u u' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact Subtype.ext (congrFun h1 k)
  · exact Subtype.ext (congrFun h2 k)

private theorem vmap_basis_linearIndependent_and_span {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ} {Ix : Type}
    [Fintype Ix] {v : Ix → (Fin n → A) × (Fin n → A)} (hli : LinearIndependent A v)
    (hsp : Submodule.span A (Set.range v) = ⊤) :
    LinearIndependent Ω (fun q => vmap A.subtype (v q)) ∧
      Submodule.span Ω (Set.range fun q => vmap A.subtype (v q)) = ⊤ := by
  classical
  obtain ⟨L, hLi, hL⟩ := exists_injective_linearMap_eq_vmap A n
  have hA : LinearIndependent A (L ∘ v) := hli.map' L (LinearMap.ker_eq_bot.2 hLi)
  have hK : LinearIndependent Ω (fun q => vmap A.subtype (v q)) := by
    have := (LinearIndependent.iff_fractionRing A Ω).1 hA
    simpa [Function.comp_def, hL] using this
  refine ⟨hK, Submodule.eq_top_of_finrank_eq ?_⟩
  rw [finrank_span_eq_card hK, ← Module.finrank_eq_card_basis (Basis.mk hli hsp.ge)]
  simp [Module.finrank_prod, Module.finrank_fin_fun]

theorem isHBasis_trans
    {x : Fin r → (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring)}
    (hx : IsHBasis (F.Bi i) x) :
    IsHBasis F.B fun j => transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x j)) := by
  obtain ⟨-, -, hbij, -⟩ := GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (F.iso i)
  delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.IsHBasis at hx ⊢
  obtain ⟨hli, hsp⟩ := vmap_basis_linearIndependent_and_span (C.v i).valuationSubring hx.1 hx.2
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, ← rhoH_trans F i] using
      hli.map' (transH (F.φ i) (F.ψ i) (F.lam i)) (LinearMap.ker_eq_bot.2 hbij.1)
  · have key : Submodule.span K (Set.range (transH (F.φ i) (F.ψ i) (F.lam i) ∘
        fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
          vmap (C.v i).valuationSubring.subtype
            (rhoH (F.Bi i) (RingOfIntegers.basis E q.2) (x q.1)))) = ⊤ := by
      rw [Set.range_comp, Submodule.span_image, hsp, Submodule.map_top,
        LinearMap.range_eq_top.2 hbij.2]
    simpa only [Function.comp_def, ← rhoH_trans F i] using key

theorem mem_stdLat_iff
    {x : Fin r → (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring)}
    (hx : IsHBasis (F.Bi i) x) (y : (Fin d → K) × (Fin d → K)) :
    y ∈ stdLat (C.v i).valuationSubring.toSubring (transH (F.φ i) (F.ψ i) (F.lam i)) ↔
      ∃ c : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → K, (∀ q, C.v i (c q) ≤ 1) ∧
        y = ∑ q, c q • rhoH F.B (RingOfIntegers.basis E q.2)
          (transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x q.1))) := by
  classical
  delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.IsHBasis at hx
  obtain ⟨L, -, hL⟩ := exists_injective_linearMap_eq_vmap (C.v i).valuationSubring d
  set T := transH (F.φ i) (F.ψ i) (F.lam i) with hT
  set bA := Basis.mk hx.1 hx.2.ge with hbA
  have hw : ∀ q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E),
      rhoH F.B (RingOfIntegers.basis E q.2) (T (vmap (C.v i).valuationSubring.subtype (x q.1))) =
        T (L (bA q)) := by
    intro q
    rw [hT, rhoH_trans F i, hL, hbA, Basis.mk_apply]
  simp_rw [hw]
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y₀, hy₀, rfl⟩ := hz
      let u : (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring) :=
        (fun k => ⟨y₀.1 k, (hy₀ k).1⟩, fun k => ⟨y₀.2 k, (hy₀ k).2⟩)
      have hu : L u = y₀ := by
        rw [hL]
        rfl
      refine ⟨fun q => (bA.repr u q : K), fun q => (Valuation.mem_valuationSubring_iff _ _).1 (bA.repr u q).2, ?_⟩
      conv_lhs => rw [← hu, ← bA.sum_repr u, map_sum, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, LinearMap.map_smul_of_tower, ← algebraMap_smul K]
      rfl
    | zero => exact ⟨0, fun q => by simp, by simp⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨c, hc, rfl⟩ := hz
      obtain ⟨c', hc', rfl⟩ := hz'
      refine ⟨c + c', fun q => Valuation.map_add_le _ (hc q) (hc' q), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
    | smul s z _ hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      refine ⟨fun q => (s : K) * c q, fun q => ?_, ?_⟩
      · rw [map_mul]
        exact mul_le_one' ((Valuation.mem_valuationSubring_iff _ _).1 s.2) (hc q)
      · rw [Subring.smul_def, Finset.smul_sum]
        simp [smul_smul]
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun q _ => ?_
    have hmem : T (L (bA q)) ∈ stdLat (C.v i).valuationSubring.toSubring T :=
      Submodule.subset_span ⟨L (bA q), fun k => ⟨by rw [hL]; exact (bA q).1 k |>.2,
        by rw [hL]; exact (bA q).2 k |>.2⟩, rfl⟩
    have := Submodule.smul_mem _ (⟨c q, (Valuation.mem_valuationSubring_iff _ _).2 (hc q)⟩ :
      (C.v i).valuationSubring.toSubring) hmem
    simpa [Subring.smul_def] using this

end Place

private theorem quot_deg_lemma_4 {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {O : Type} [CommRing O] {J : Type} [Fintype J]
    (b : Basis J ℤ O) (ρ : O →+* Module.End K V) (χ : O →+* K) (H : C.I → AddSubgroup V)
    (hH : GlobalTheory.CompanionTheory.Ar.Crv.IsBun C H) (hχ : ∀ (i : C.I) (a : O), C.v i (χ a) ≤ 1) {r : ℕ}
    (x₀ : Fin r → V)
    (h₀li : LinearIndependent K fun q : Fin r × J => ρ (b q.2) (x₀ q.1))
    (h₀sp : Submodule.span K (Set.range fun q : Fin r × J => ρ (b q.2) (x₀ q.1)) = ⊤)
    (y : C.I → Fin r → V)
    (hyli : ∀ i, LinearIndependent K fun q : Fin r × J => ρ (b q.2) (y i q.1))
    (hysp : ∀ i, Submodule.span K (Set.range fun q : Fin r × J => ρ (b q.2) (y i q.1)) = ⊤)
    (hL : ∀ i z, z ∈ H i ↔ ∃ c : Fin r × J → K, (∀ q, C.v i (c q) ≤ 1) ∧
      z = ∑ q, c q • ρ (b q.2) (y i q.1))
    (N : C.I → Matrix (Fin r) (Fin r) K)
    (hN : ∀ i j, y i j - ∑ l, N i j l • x₀ l ∈ eigSpan ρ χ)
    (h0 : GlobalTheory.CompanionTheory.Ar.Crv.deg C (GlobalTheory.CompanionTheory.Ar.Crv.quot C H (eigSpan ρ χ)) = 0) :
    (∀ i, (N i).det ≠ 0) ∧ {i | C.v i (N i).det ≠ 1}.Finite ∧
      ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (N i).det) = 0 := by
  classical
  obtain ⟨b₀, hb₀, -⟩ := exists_quot_basis b ρ χ x₀ h₀li h₀sp
  choose bq hbq1 hbq2 using fun i => exists_quot_basis b ρ χ (y i) (hyli i) (hysp i)
  have hLat : ∀ i, GlobalTheory.CompanionTheory.Ar.Crv.IsLatOf C i (bq i) (GlobalTheory.CompanionTheory.Ar.Crv.quot C H (eigSpan ρ χ) i) :=
    fun i => isLatOf_quot b ρ χ i (bq i) (H i) (hχ i) (hbq2 i) (hL i)
  have hBun := (GlobalTheory.T.sub_and_quotient_bundles K C V H (eigSpan ρ χ) hH).2
  obtain ⟨hfin, hdeg⟩ :=
    GlobalTheory.T.bundle_degree_eq_sum_valuations K C _ (GlobalTheory.CompanionTheory.Ar.Crv.quot C H (eigSpan ρ χ)) r b₀ bq hBun hLat
  have hdet : ∀ i, b₀.det (bq i) = (N i).det := by
    intro i
    have hbqN : ∀ j, bq i j = ∑ l, N i j l • b₀ l := by
      intro j
      rw [hbq1 i j]
      simp_rw [hb₀]
      rw [show (∑ l, N i j l • (eigSpan ρ χ).mkQ (x₀ l)) =
          (eigSpan ρ χ).mkQ (∑ l, N i j l • x₀ l) by rw [map_sum]; simp only [map_smul]]
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hN i j
    have hM : b₀.toMatrix (bq i) = (N i).transpose := by
      ext a j
      rw [Basis.toMatrix_apply, hbqN, Matrix.transpose_apply, ← Basis.equivFun_symm_apply,
        ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [Basis.det_apply, hM, Matrix.det_transpose]
  refine ⟨fun i => ?_, ?_, ?_⟩
  · rw [← hdet i]
    exact (b₀.isUnit_det (bq i)).ne_zero
  · simpa only [hdet] using hfin
  · rw [hdeg] at h0
    simpa only [hdet] using h0

theorem curve_deg : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d r : ℕ) (F : Family C p d (𝓞 E)) (χ : 𝓞 E →+* K), (∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits) → (∀ (i : C.I) (a : 𝓞 E), C.v i (χ a) ≤ 1) → ∀ (x₀ : Fin r → (Fin d → K) × (Fin d → K)) (x : ∀ i : C.I, Fin r → (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring)) (N : C.I → Matrix (Fin r) (Fin r) K), IsHBasis F.B x₀ → (∀ i, IsHBasis (F.Bi i) (x i)) → (∀ i j, transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i j)) - ∑ l, N i j l • x₀ l ∈ eigW F.B χ) → (∀ i, (N i).det ≠ 0) ∧ {i | C.v i (N i).det ≠ 1}.Finite ∧ ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (N i).det) = 0 := by
  intro E _ _ _ K _ C p _ _ d r F χ hspl hχ x₀ x N hx₀ hx hN
  classical
  rcases isEmpty_or_nonempty C.I with hI | hI
  · refine ⟨fun i => (IsEmpty.false i).elim,
      Set.finite_empty.subset fun i _ => (IsEmpty.false i).elim, ?_⟩
    rw [finsum_of_isEmpty]
  obtain ⟨D, hDρ, hDH⟩ := GlobalTheory.T.family_hodge_lattice_data K C p d (𝓞 E) F hI
  have hW : eigW F.B χ = eigSpan D.ρH χ := by
    delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.eigW
    simp only [eigSpan, hDρ]
  obtain ⟨h₀li, h₀sp⟩ := hx₀
  have hHB := fun i => isHBasis_trans F i (hx i)
  have hL : ∀ i y, y ∈ D.H i ↔ ∃ c : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → K,
      (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • D.ρH (RingOfIntegers.basis E q.2)
        (transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i q.1))) := by
    intro i y
    rw [hDH i y, mem_stdLat_iff F i (hx i) y]
    simp only [hDρ]
  have hyli : ∀ i, LinearIndependent K fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      D.ρH (RingOfIntegers.basis E q.2)
        (transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i q.1))) := by
    intro i
    obtain ⟨h1, -⟩ := hHB i
    simpa only [hDρ] using h1
  have hysp : ∀ i, Submodule.span K (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      D.ρH (RingOfIntegers.basis E q.2)
        (transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i q.1)))) = ⊤ := by
    intro i
    obtain ⟨-, h2⟩ := hHB i
    simpa only [hDρ] using h2
  have h0 := GlobalTheory.T.split_hermitian_generators_exist E K C p d r D χ hspl fun i =>
    ⟨fun j => transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i j)),
      hyli i, hL i⟩
  exact quot_deg_lemma_4 C (RingOfIntegers.basis E) D.ρH χ D.H D.H_bun hχ x₀
    (by simpa only [hDρ] using h₀li) (by simpa only [hDρ] using h₀sp)
    (fun i j => transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i j)))
    hyli hysp hL N (fun i j => by rw [← hW]; exact hN i j) h0

end GlobalTheory.CompanionTheory.Ar.Flat.DegProd
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_bounded_frame : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d r : ℕ) (F : Family C p d (𝓞 E)) (χ : 𝓞 E →+* K), (∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits) → (∀ (i : C.I) (a : 𝓞 E), C.v i (χ a) ≤ 1) → ∀ (x₀ : Fin r → (Fin d → K) × (Fin d → K)) (x : ∀ i : C.I, Fin r → (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring)) (N : C.I → Matrix (Fin r) (Fin r) K), IsHBasis F.B x₀ → (∀ i, IsHBasis (F.Bi i) (x i)) → (∀ i j, transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i j)) - ∑ l, N i j l • x₀ l ∈ eigW F.B χ) → (∀ i, (N i).det ≠ 0) ∧ {i | C.v i (N i).det ≠ 1}.Finite ∧ ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (N i).det) = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.DegProd.curve_deg
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in

theorem toH_rhoH {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X : Scheme.{0}}
    {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d r : ℕ} {M : LieModel t.G ξ (Fin d → Ω)} (S : GermSys t ξ M)
    {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {𝓗 : HodgeLat M.lat ρ H.bar r} (hg : S.Gives 𝓗) (p : Cpt ξ) (a : 𝓞 E)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (rhoH (S.g p).B a y) = 𝓗.ρH a (toH S p y) := by
  have h1 := (GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.2.2.1 a
  have h2 := hg.1 a (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))
  have h3 := LinearMap.congr_fun h1 (vmap (genMap ξ p) y)
  simp only [LinearMap.comp_apply] at h3
  have h4 := vmap_rhoH (S.mapK p) a y
  refine (congrArg (fun z => toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) z)) h4).trans ?_
  refine (congrArg (toVec Ω d) h3.symm).trans ?_
  exact h2.symm

open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in

theorem eigProj_toH_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
    {X : Scheme.{0}} {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d r : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}
    (S : GermSys t ξ M) {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {𝓗 : HodgeLat M.lat ρ H.bar r} (hg : S.Gives 𝓗)
    (σ : E →+* Ω) (p : Cpt ξ) (τ : 𝓞 E →+* X.presheaf.stalk p.1) (hτ : ∀ a, genMap ξ p (τ a) = σ (a : E))
    {w : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)} (hw : w ∈ eigW (S.g p).B τ) :
    HT.eigProj 𝓗.ρH σ (toH S p w) = 0 := by
  refine eigW_induction (P := fun w => HT.eigProj 𝓗.ρH σ (toH S p w) = 0) hw ?_ ?_ ?_
  · intro a y
    have hc : HT.eigProj 𝓗.ρH σ (𝓗.ρH a (toH S p y)) = 𝓗.ρH a (HT.eigProj 𝓗.ρH σ (toH S p y)) := by
      simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    have hm := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem 𝓗.ρH σ (toH S p y)) a
    have e1 : toH S p (rhoH (S.g p).B a y - τ a • y) = 𝓗.ρH a (toH S p y) - σ (a : E) • toH S p y :=
      (toH_sub S p _ _).trans (congrArg₂ (· - ·) (toH_rhoH S hg p a y)
        ((toH_smul S p _ _).trans (congrArg (· • toH S p y) (hτ a))))
    refine (congrArg _ e1).trans ?_
    generalize toH S p y = v at hc hm
    rw [map_sub, map_smul, hc, hm, sub_self]
  · exact (congrArg _ (toH_zero S p)).trans (map_zero _)
  · intro y y' h1 h2
    refine (congrArg _ (toH_add S p y y')).trans ?_
    exact (map_add _ _ _).trans (by rw [h1, h2, add_zero])

end GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in

theorem exists_trans {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
    {X : Scheme.{0}} {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d r : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}
    (S : GermSys t ξ M) {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {𝓗 : HodgeLat M.lat ρ H.bar r} (hg : S.Gives 𝓗)
    (σ : E →+* Ω) (p q : Cpt ξ) (h : q.1 ⤳ p.1) (τ : 𝓞 E →+* X.presheaf.stalk q.1)
    (hτ : ∀ a, genMap ξ q (τ a) = σ (a : E)) {φ' ψ' : Germ.Pt (X.presheaf.stalk q.1) 1 d}
    {lam' : Germ.PS (X.presheaf.stalk q.1) 2 d}
    (he : transH (S.φ p) (S.ψ p) (S.lam p) = transH (S.φ q) (S.ψ q) (S.lam q) ∘ₗ
      transH (fun i => MvPowerSeries.map (genMap ξ q) (φ' i)) (fun i => MvPowerSeries.map (genMap ξ q) (ψ' i))
        (MvPowerSeries.map (genMap ξ q) lam'))
    {xp : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)}
    {xq : Fin r → (Fin d → X.presheaf.stalk q.1) × (Fin d → X.presheaf.stalk q.1)}
    (hxq : IsHBasis (S.g q).B xq) {u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)}
    (hu : LinearIndependent Ω u) {Ap Aq : Matrix (Fin r) (Fin r) Ω}
    (hAp : ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (xp j)) = ∑ l, Ap j l • u l)
    (hAq : ∀ j, HT.eigProj 𝓗.ρH σ (toH S q (xq j)) = ∑ l, Aq j l • u l) :
    ∃ Mt : Matrix (Fin r) (Fin r) (X.presheaf.stalk q.1), Ap = Mt.map (genMap ξ q) * Aq ∧
      ∀ j, transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)) - ∑ l, Mt j l • xq l ∈
        eigW (S.g q).B τ := by
  choose m hm using fun j => exists_sub_mem_eigW hxq τ
    (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)))
  refine ⟨Matrix.of m, ?_, hm⟩
  have key : ∀ j, ∑ k, Ap j k • u k = ∑ k, ((Matrix.of m).map (genMap ξ q) * Aq) j k • u k := by
    intro j
    have h0 := eigProj_toH_eq_zero S hg σ q τ hτ (hm j)
    have h1 : toH S q (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)) - ∑ l, m j l • xq l) =
        toH S p (xp j) - ∑ l, genMap ξ q (m j l) • toH S q (xq l) := by
      refine (toH_sub S q _ _).trans (congrArg₂ (· - ·) (toH_spec S p q h he (xp j)).symm ?_)
      exact (toH_sum _ S q _).trans (Finset.sum_congr rfl fun l _ => toH_smul S q _ _)
    have h2 := (congrArg (HT.eigProj 𝓗.ρH σ) h1).symm.trans h0
    rw [map_sub, sub_eq_zero, map_sum] at h2
    refine ((hAp j).symm.trans h2).trans ?_
    simp only [map_smul, hAq, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, Matrix.map_apply, Matrix.of_apply,
      smul_smul]
    exact Finset.sum_comm
  ext j k
  have := (Fintype.linearIndependent_iff.1 hu) (fun k => Ap j k - ((Matrix.of m).map (genMap ξ q) * Aq) j k)
    (by simp only [sub_smul, Finset.sum_sub_distrib, key j, sub_self]) k
  exact sub_eq_zero.1 this

end GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in

theorem germ_degZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Sp O) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : O) (p : ℕ) (σ : E →+* Ω), Irreducible ϖ → p.Prime → ϖ ∣ (p : O) → ξ ≫ s = spMap (algebraMap O Ω) → IsCptGen ξ → PowFns t → S.Gives 𝓗 → (∀ q : Cpt ξ, (p : X.residueField q.1) = 0 → FibPF t q.1) → Nat.card (E →+* Ω) = Module.finrank ℚ E → (∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) → 𝓗.DegZero σ (algebraMap O Ω ϖ) := by
  intro E _ _ _ H _ hstar X t Ω _ _ ξ d r M S ρ 𝓗 O _ _ _ _ s _ _ ϖ p σ hϖ hp hdvd hs hξ hpow hgive hfib hcard hrange
    u hu hsp Γ
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (algebraMap O Ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ
    have h1 : algebraMap O Ω ϖ ^ n = 0 := by rw [← map_pow, ← hw, map_mul, hx, zero_mul]
    have h0 : algebraMap O Ω ϖ = 0 := (pow_eq_zero_iff (fun hn => by simp [hn] at h1)).1 h1
    obtain ⟨c, hc⟩ := hdvd
    have h2 := congrArg (algebraMap O Ω) hc
    rw [map_natCast, map_mul, h0, zero_mul] at h2
    exact hp.ne_zero (by exact_mod_cast h2)
  have hreg := GlobalTheory.T.base_constants_regular X Ω ξ O s hs
  have hσ : ∀ (q : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ q := fun q a => by
    obtain ⟨o, ho⟩ := hrange σ a
    exact ho ▸ hreg q o
  let τ : ∀ q : Cpt ξ, 𝓞 E →+* X.presheaf.stalk q.1 := fun q =>
    (GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv ξ hξ q).symm.toRingHom.comp
      ((σ.comp (algebraMap (𝓞 E) E)).codRestrict (regAt ξ q) (hσ q))
  have hτ : ∀ (q : Cpt ξ) (a : 𝓞 E), genMap ξ q (τ q a) = σ (a : E) := fun q a => by
    have := GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv_coe ξ hξ q (τ q a)
    rw [← this]
    simp [τ]
  let q0 : Cpt ξ := ⟨centre Γ.η, Γ.η_spec⟩
  let qi : Γ.C.I → Cpt ξ := fun i => ⟨centre (Γ.z i), FibreCurve.z_spec Γ i⟩
  let v0 : X.presheaf.stalk q0.1 →+* Γ.κ := (Scheme.stalkClosedPointTo Γ.η).hom
  let vi : ∀ i, X.presheaf.stalk (qi i).1 →+* (Γ.C.v i).valuationSubring :=
    fun i => (Scheme.stalkClosedPointTo (Γ.z i)).hom
  have hpκ : (p : Γ.κ) = 0 := by
    obtain ⟨hh, s0, hs0, hs1⟩ := Γ.η_zero
    obtain ⟨c, hc⟩ := hdvd
    obtain ⟨c', hc'⟩ := hreg q0 c
    have e : (p : X.presheaf.stalk q0.1) = s0 * c' := hξ.inj q0 (by
      have h2 := congrArg (algebraMap O Ω) hc
      rw [map_natCast, map_mul] at h2
      rw [map_natCast, map_mul, h2, hc']
      exact congrArg (· * algebraMap O Ω c) hs0.symm)
    have h3 := congrArg v0 e
    rw [map_natCast, map_mul] at h3
    rw [h3]
    have h4 : v0 s0 = 0 := hs1
    rw [h4, zero_mul]
  haveI : CharP Γ.κ p := (CharP.charP_iff_prime_eq_zero hp).2 hpκ
  obtain ⟨F, hF0, hFi⟩ := GlobalTheory.T.fibre_curve_germ_powers E H hstar X t Ω ξ d M S O s _ p Γ hξ hpow hfib
  choose hFB φ' ψ' lam' he hφ hψ hlam using hFi
  choose xs A hxs hfr hpr using GlobalTheory.T.hodge_lattice_germ_eigen E H X t Ω ξ d r M S ρ 𝓗 σ u hξ hgive hσ hu hsp
  have hdet := fun q => (GlobalTheory.T.hodge_lattice_span_independent X Ω ξ E (Fin d → Ω) M.lat ρ H.bar r 𝓗 σ u hσ hu hsp).2.2 q (A q) (hfr q)
  choose Mt hAM hMt using fun i => exists_trans S hgive σ (qi i) q0 (FibreCurve.generic_centre_specializes Γ i) (τ q0) (hτ q0)
    (he i) (hxs q0) hu (hpr (qi i)) (hpr q0)
  let χ : 𝓞 E →+* Γ.κ := v0.comp (τ q0)
  have hsq : ∀ i, ((Γ.C.v i).valuationSubring.subtype).comp (vi i) =
      v0.comp (X.presheaf.stalkSpecializes (FibreCurve.generic_centre_specializes Γ i)).hom := fun i => by
    have key := ProjectiveLinePlaces.stalk_square (FibreCurve.generic_centre_specializes Γ i) (Scheme.stalkClosedPointTo (Γ.z i))
      (Scheme.stalkClosedPointTo Γ.η) (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype)
      ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk Γ.η).trans ((Γ.z_gen i).symm.trans
        (congrArg (Spec.map (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype) ≫ ·)
          (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (Γ.z i))).symm))
    exact RingHom.ext fun s => (congrArg (fun g => g.hom s) key).symm
  have hτs : ∀ i a, (X.presheaf.stalkSpecializes (FibreCurve.generic_centre_specializes Γ i)).hom (τ (qi i) a) = τ q0 a :=
    fun i a => hξ.inj q0 ((ProjectiveLinePlaces.genMap_specializes (FibreCurve.generic_centre_specializes Γ i) q0.2 (qi i).2 _).trans
      ((hτ (qi i) a).trans (hτ q0 a).symm))
  have hχ : ∀ i a, Γ.C.v i (χ a) ≤ 1 := fun i a => by
    have e : χ a = ((vi i (τ (qi i) a) : (Γ.C.v i).valuationSubring) : Γ.κ) :=
      (congrArg v0 (hτs i a).symm).trans (RingHom.congr_fun (hsq i) (τ (qi i) a)).symm
    rw [e]
    exact (vi i (τ (qi i) a)).2
  let x₀ : Fin r → (Fin d → Γ.κ) × (Fin d → Γ.κ) := fun l => vmap v0 (xs q0 l)
  let x : ∀ i : Γ.C.I, Fin r → (Fin d → (Γ.C.v i).valuationSubring) × (Fin d → (Γ.C.v i).valuationSubring) :=
    fun i j => vmap (vi i) (xs (qi i) j)
  let N : Γ.C.I → Matrix (Fin r) (Fin r) Γ.κ := fun i => (Mt i).map v0
  have hx₀ : IsHBasis F.B x₀ := GlobalTheory.T.intersection_second E _ _ v0 d r _ _ _ hF0 (hxs q0)
  have hx : ∀ i, IsHBasis (F.Bi i) (x i) := fun i => GlobalTheory.T.intersection_second E _ _ (vi i) d r _ _ _ (hFB i) (hxs (qi i))
  have hrel : ∀ i j, transH (F.φ i) (F.ψ i) (F.lam i) (vmap (Γ.C.v i).valuationSubring.subtype (x i j)) -
      ∑ l, N i j l • x₀ l ∈ eigW F.B χ := fun i j => by
    have h1 := vmap_mem_eigW hF0 (τ q0) (hMt i j)
    have h2 := vmap_rel v0 (vi i) (Γ.C.v i).valuationSubring.subtype _ (hsq i) (φ' i) (ψ' i) (lam' i)
      (xs (qi i) j) (Mt i j) (xs q0)
    rw [hφ i, hψ i, hlam i]
    exact h2 ▸ h1
  obtain ⟨hne, hfin, hsum⟩ := GlobalTheory.T.valuation_bounded_frame E Γ.κ Γ.C p d r F χ
    (GlobalTheory.T.charpoly_splits_of_embeddings E Ω O Γ.κ (v0.comp ((GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv ξ hξ q0).symm.toRingHom.comp
      ((algebraMap O Ω).codRestrict (regAt ξ q0) (hreg q0)))) hinj hcard hrange) hχ x₀ x N hx₀ hx hrel
  have hNdet : ∀ i, (N i).det = v0 (Mt i).det := fun i => (RingHom.map_det v0 (Mt i)).symm
  have hAdet : ∀ i, (A (qi i)).det = genMap ξ q0 (Mt i).det * (A q0).det := fun i => by
    rw [hAM i, Matrix.det_mul]
    exact congrArg (· * (A q0).det) (RingHom.map_det (genMap ξ q0) (Mt i)).symm
  have hunit : ∀ i, IsUnit (Mt i).det := fun i => by
    have h1 : IsUnit (v0 (Mt i).det) := isUnit_iff_ne_zero.2 (hNdet i ▸ hne i)
    haveI : IsLocalHom v0 := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo Γ.η).hom)
    exact (isUnit_map_iff v0 _).1 h1
  refine ⟨(A q0).det, fun i => (A (qi i)).det, fun i => ((N i).det)⁻¹, hdet q0,
    fun i => ⟨FibreCurve.z_spec Γ i, hdet (qi i)⟩, fun i => ⟨inv_ne_zero (hne i), ?_⟩, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hunit i
    have hw0 : genMap ξ q0 (w : X.presheaf.stalk q0.1) * genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hv0 : v0 (w : X.presheaf.stalk q0.1) * v0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine ⟨Γ.η_spec, ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1), ?_, ?_⟩
    · have e0 := (hdet q0).1
      have e1 : (A (qi i)).det = genMap ξ q0 (w : X.presheaf.stalk q0.1) * (A q0).det :=
        (hAdet i).trans (congrArg (fun z => genMap ξ q0 z * (A q0).det) hw.symm)
      have e2 : genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) =
          (A q0).det / (genMap ξ q0 (w : X.presheaf.stalk q0.1) * (A q0).det) := by
        generalize genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = b at hw0
        generalize genMap ξ q0 (w : X.presheaf.stalk q0.1) = a at hw0
        have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hw0
        rw [eq_div_iff (mul_ne_zero ha e0)]
        linear_combination (A q0).det * hw0
      exact e2.trans (congrArg ((A q0).det / ·) e1.symm)
    · have e3 : (N i).det = v0 (w : X.presheaf.stalk q0.1) := (hNdet i).trans (congrArg v0 hw.symm)
      exact (eq_inv_of_mul_eq_one_right hv0).trans (congrArg (·⁻¹) e3.symm)
  · refine hfin.subset fun i hi h1 => hi ?_
    rw [map_inv₀, h1, inv_one]
  · have : ∀ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i ((N i).det)⁻¹)) =
        (Γ.C.w i : ℤ) * WithZero.log (Γ.C.v i (N i).det) := fun i => by
      rw [map_inv₀, WithZero.log_inv, neg_neg]
    simp only [this]
    exact hsum

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
