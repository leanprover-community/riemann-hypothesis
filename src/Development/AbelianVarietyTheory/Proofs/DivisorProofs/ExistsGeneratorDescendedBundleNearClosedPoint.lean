import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFarSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointsLiftMulInvStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfLocalAffineCover

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GenRestrict

theorem exists_gen_restrict : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (O O' : Z.Opens), O ≤ O' →
    ∀ u : LB.Sec (L.pull O'.ι), (∀ z : O'.toScheme, O'.ι z ∈ O → z ∈ nonzeroLocus u) →
    ∃ t : LB.Gen (L.pull O.ι), t.IsGen := by
  intro Z L _ O O' hle u hu
  have e : ∀ _k : PUnit, Z.homOfLE hle ≫ (fun _ : PUnit => O'.ι) _k = (fun _ : PUnit => O.ι) _k :=
    fun _ => Scheme.homOfLE_ι Z hle
  let v : LB.Sec (L.pull O.ι) := PullbackSections.pullSecLC L _ _ _ (Z.homOfLE hle) e u
  refine GlobalTheory.LocusPull.exists_gen_of_nonzeroLocus_eq_top v (top_unique fun z _ => ?_)
  have heq : O'.ι (Z.homOfLE hle z) = O.ι z := by
    exact congrArg (fun f : O.toScheme ⟶ Z => f z) (Scheme.homOfLE_ι Z hle)
  have hz : O'.ι (Z.homOfLE hle z) ∈ O := by
    rw [heq]
    exact (Scheme.Opens.ι_apply O z).symm ▸ z.2
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu _ hz)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  show z ∈ O.toScheme.basicOpen ((Scheme.Hom.appLE (Z.homOfLE hle) _ _ _).hom (u.f k))
  rw [Scheme.basicOpen_appLE]
  refine ⟨?_, hk⟩
  have h1 : Z.homOfLE hle z ∈ (L.pull O'.ι).U k := Scheme.basicOpen_le _ _ hk
  refine mem_pull.2 ?_
  rw [← heq]
  exact mem_pull.1 h1

end GlobalTheory.GenRestrict
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (O O' : Z.Opens), O ≤ O' → ∀ u : LB.Sec (L.pull O'.ι), (∀ z : O'.toScheme, O'.ι z ∈ O → z ∈ nonzeroLocus u) → ∃ t : LB.Gen (L.pull O.ι), t.IsGen := by
  atlas_forward_decl GlobalTheory.GenRestrict.exists_gen_restrict
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_nhds_nonzero_of_isClosedMap :
    ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), IsClosedMap p.base → ∀ (L : LB Z) (V : Y.Opens) (u : LB.Sec (L.pull (p ⁻¹ᵁ V).ι)) (y : Y), y ∈ V → (∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) = y → z ∈ nonzeroLocus u) → ∃ V₁ : Y.Opens, y ∈ V₁ ∧ V₁ ≤ V ∧ ∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) ∈ V₁ → z ∈ nonzeroLocus u := by
  intro Z Y p hp L V u y hy h
  have hO : IsOpen ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme)) :=
    (p ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap _ (nonzeroLocus u).isOpen
  have hC : IsClosed (p.base '' ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme))ᶜ) :=
    hp _ hO.isClosed_compl
  refine ⟨V ⊓ ⟨_, hC.isOpen_compl⟩, ⟨hy, ?_⟩, inf_le_left, ?_⟩
  · rintro ⟨c, hc, hcy⟩
    have hcV : c ∈ p ⁻¹ᵁ V := by
      change p c ∈ V
      have : p c = y := hcy
      rw [this]; exact hy
    exact hc ⟨⟨c, hcV⟩, h ⟨c, hcV⟩ hcy, rfl⟩
  · intro z hz
    have h2 : (p ⁻¹ᵁ V).ι z ∈ (p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme) := by
      by_contra hn
      exact hz.2 ⟨_, hn, rfl⟩
    obtain ⟨w, hw, hwz⟩ := h2
    have : w = z := (p ⁻¹ᵁ V).ι.isOpenEmbedding.injective hwz
    subst this
    exact hw

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), IsClosedMap p.base → ∀ (L : LB Z) (V : Y.Opens) (u : LB.Sec (L.pull (p ⁻¹ᵁ V).ι)) (y : Y), y ∈ V → (∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) = y → z ∈ nonzeroLocus u) → ∃ V₁ : Y.Opens, y ∈ V₁ ∧ V₁ ≤ V ∧ ∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) ∈ V₁ → z ∈ nonzeroLocus u := by
  atlas_forward_decl GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ClosedPt

lemma exists_max_specializes {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) (x : Y)
    (hx : x ∈ V) : ∃ N : PrimeSpectrum Γ(Y, V), N.asIdeal.IsMaximal ∧
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≤ N.asIdeal ∧ x ⤳ hV.fromSpec N := by
  obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    (hV.primeIdealOf ⟨x, hx⟩).isPrime.ne_top
  refine ⟨⟨N, hN.isPrime⟩, hN, hle, ?_⟩
  have h1 : (hV.primeIdealOf ⟨x, hx⟩) ⤳ (⟨N, hN.isPrime⟩ : PrimeSpectrum Γ(Y, V)) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have h2 := Specializes.map (f := hV.fromSpec) h1 hV.fromSpec.continuous
  rwa [hV.fromSpec_primeIdealOf] at h2

lemma fromSpec_mem {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V)
    (N : PrimeSpectrum Γ(Y, V)) : hV.fromSpec N ∈ V := by
  have : hV.fromSpec N ∈ Set.range hV.fromSpec := ⟨N, rfl⟩
  rwa [hV.range_fromSpec] at this

theorem exists_closed_point : ∀ (Y : Scheme.{0}) (x : Y), ∃ V : Y.Opens, IsAffineOpen V ∧ ∃ y ∈ V, x ⤳ y ∧ ∀ V₂ : Y.Opens, V₂ ≤ V → IsAffineOpen V₂ → y ∈ V₂ → (∀ y₁ ∈ V₂, y ⤳ y₁ → y₁ = y) ∧ ∃ M : Ideal Γ(Y, V₂), M.IsMaximal ∧ ∀ a : Γ(Y, V₂), a ∈ M ↔ y ∉ Y.basicOpen a := by
  intro Y x
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤) trivial
  obtain ⟨N, hN, -, hxN⟩ := exists_max_specializes hV x hx
  refine ⟨V, hV, hV.fromSpec N, fromSpec_mem hV N, hxN, ?_⟩
  intro V₂ hle hV₂ hy
  have hcl : ∀ y₁ ∈ V₂, hV.fromSpec N ⤳ y₁ → y₁ = hV.fromSpec N := by
    intro y₁ hy₁ hs
    have e := hV.fromSpec_primeIdealOf ⟨y₁, hle hy₁⟩
    have hs' : hV.fromSpec N ⤳ hV.fromSpec (hV.primeIdealOf ⟨y₁, hle hy₁⟩) := by
      rw [e]; exact hs
    have h3 : N ⤳ hV.primeIdealOf ⟨y₁, hle hy₁⟩ :=
      (hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp hs'
    have h4 : N ≤ hV.primeIdealOf ⟨y₁, hle hy₁⟩ := (PrimeSpectrum.le_iff_specializes _ _).mpr h3
    have h5 : N = hV.primeIdealOf ⟨y₁, hle hy₁⟩ :=
      PrimeSpectrum.ext (hN.eq_of_le (hV.primeIdealOf ⟨y₁, hle hy₁⟩).isPrime.ne_top h4)
    rw [h5]; exact e.symm
  refine ⟨hcl, (hV₂.primeIdealOf ⟨_, hy⟩).asIdeal, ?_, ?_⟩
  · obtain ⟨N₂, hN₂, -, hs⟩ := exists_max_specializes hV₂ _ hy
    have e := hcl _ (fromSpec_mem hV₂ N₂) hs
    have e2 := hV₂.fromSpec_primeIdealOf ⟨_, hy⟩
    have : N₂ = hV₂.primeIdealOf ⟨_, hy⟩ :=
      hV₂.fromSpec.isOpenEmbedding.injective (e.trans e2.symm)
    rw [← this]; exact hN₂
  · intro a
    have e2 := hV₂.fromSpec_primeIdealOf ⟨_, hy⟩
    have h := hV₂.fromSpec_preimage_basicOpen a
    have h' : hV₂.fromSpec (hV₂.primeIdealOf ⟨_, hy⟩) ∈ Y.basicOpen a ↔
        hV₂.primeIdealOf ⟨_, hy⟩ ∈ PrimeSpectrum.basicOpen a := by
      rw [← h]; rfl
    rw [e2, PrimeSpectrum.mem_basicOpen] at h'
    exact (not_iff_comm.mp h'.symm).symm

end GlobalTheory.ClosedPt
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialization_closed_in_affine_neighbourhood : ∀ (Y : Scheme.{0}) (x : Y), ∃ V : Y.Opens, IsAffineOpen V ∧ ∃ y ∈ V, x ⤳ y ∧ ∀ V₂ : Y.Opens, V₂ ≤ V → IsAffineOpen V₂ → y ∈ V₂ → (∀ y₁ ∈ V₂, y ⤳ y₁ → y₁ = y) ∧ ∃ M : Ideal Γ(Y, V₂), M.IsMaximal ∧ ∀ a : Γ(Y, V₂), a ∈ M ↔ y ∉ Y.basicOpen a := by
  atlas_forward_decl GlobalTheory.ClosedPt.exists_closed_point
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_local_baseChange_of_proper_properties : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsFinite k ∧ QuasiCompact p' ∧ QuasiSeparated p' ∧ Function.Surjective k'.base ∧ IsClosedMap (p' ≫ k).base ∧ IsClosedMap p.base ∧ (∀ V : Y.Opens, IsAffineOpen V → IsCompact (p ⁻¹ᵁ V : Set Z) ∧ IsQuasiSeparated (p ⁻¹ᵁ V : Set Z)) ∧ ∃ (d : ℕ) (b : Fin d → R'), ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, ρ (c l) * b l := by
  first | exact @GlobalTheory.finiteFlat_proper_baseChange_facts | exact GlobalTheory.finiteFlat_proper_baseChange_facts | (intros; apply GlobalTheory.finiteFlat_proper_baseChange_facts <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fibre_and_eq_of_specializes_of_isFinite' : ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y, {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by
  first | exact @GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite | exact GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite | (intros; apply GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem exists_separating_basicOpen_functions : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  intro X U hU F hFU hsp W hW
  classical
  have key : ∀ a ∈ F, ∃ g : Γ(X, U), a ∈ X.basicOpen g ∧ X.basicOpen g ≤ W a ∧
      ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen g := by
    intro a ha
    let C : Set X := ⋃ b ∈ F.erase a, closure {b}
    have hC : IsClosed C := isClosed_biUnion_finset (fun b _ => isClosed_closure)
    let V : X.Opens := W a ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
    have haC : a ∉ C := by
      simp only [C, Set.mem_iUnion, not_exists]
      intro b hb hab
      have hb' := Finset.mem_erase.mp hb
      exact hb'.1 (hsp b hb'.2 a ha (specializes_iff_mem_closure.mpr hab))
    have haV : a ∈ V := ⟨hW a ha, haC⟩
    obtain ⟨g, hgV, hag⟩ := hU.exists_basicOpen_le ⟨a, haV⟩ (hFU a ha)
    refine ⟨g, hag, le_trans hgV inf_le_left, ?_⟩
    intro b hb hba hbg
    have hbV : b ∈ V := hgV hbg
    apply hbV.2
    simp only [C, Set.mem_iUnion]
    exact ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, subset_closure rfl⟩
  choose! f hf using key
  exact ⟨f, hf⟩

end GlobalTheory

alias _root_.GlobalTheory.T.exists_separating_basicOpen_functions' := _root_.GlobalTheory.exists_separating_basicOpen_functions
end

section
noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.BdDim.GenCover
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LBGerm GlobalTheory.AmpleOverBase
variable {X Y : Scheme.{0}}

theorem exists_sec_of_pull [CompactSpace X] [QuasiSeparatedSpace X] {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    [IsOpenImmersion f] (r : Γ(X, ⊤)) (hr : X.basicOpen r = f.opensRange) {n : ℕ} (t : (lbPow (L.pull f) n).Sec)
    (y : Y) (hty : y ∈ nonzeroLocus t) : ∃ s : (lbPow L n).Sec, f y ∈ nonzeroLocus s := by
  have hs₀ : nonzeroLocus (secOfFn L r) = f.opensRange := (nonzeroLocus_secOfFn hL r).trans hr
  obtain ⟨T, hT, hTu⟩ := exists_push f (nonzeroLocus (secOfFn L r)) hs₀ t
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul hL (secOfFn L r) T hT
  obtain ⟨u, hu⟩ := hN N le_rfl
  have key : ∀ (y' : Y) (J : PUnit → L.ι), f y' ∈ powChart L J →
      (f y' ∈ nonzeroLocus u ↔ y' ∈ nonzeroLocus t) := fun y' J hJ => by
    have hs : f y' ∈ nonzeroLocus (secOfFn L r) := hs₀ ▸ ⟨y', rfl⟩
    have hy : f y' ∈ nonzeroLocus (secOfFn L r) ⊓ powChart L J := ⟨hs, hJ⟩
    have e := congrArg (gs (𝟙 X) (f y') _) (hu J)
    rw [gs_res (𝟙 X) (f y') _ hy, gs_mul (𝟙 X) (f y') _ hy, gs_pow (𝟙 X) (f y') _ hy, gs_res (𝟙 X) (f y') _ hy] at e
    rw [mem_nonzeroLocus_iff_powFn u hJ, e, IsUnit.mul_iff, hTu y' J hJ]
    exact and_iff_right (((mem_nonzeroLocus_iff_powFn _ hJ).1 hs).pow N)
  obtain ⟨i, hi⟩ := exists_chart hL (f y)
  refine ⟨secCast (by omega) u, ?_⟩
  rw [nonzeroLocus_secCast]
  exact (key y (fun _ => i) (mem_powChart.2 hi)).2 hty

theorem exists_isGenerated_pow_of_basicOpen_cover : ∀ (X : Scheme.{0}) (O : Type) [CommRing O] (I : Type) [Finite I]
    (Y : I → Scheme.{0}) (s : X ⟶ Sp O) (u : ∀ i, Y i ⟶ X) (a : I → O) (L : LB X),
    CompactSpace X → QuasiSeparatedSpace X → L.IsLB → Ideal.span (Set.range a) = ⊤ →
    (∀ i, IsOpenImmersion (u i)) → (∀ i, Set.range (u i) = s ⁻¹' {x : Sp O | a i ∉ x.asIdeal}) →
    (∀ i, ∃ N : ℕ, 0 < N ∧ IsGenerated (lbPow (L.pull (u i)) N)) → ∃ m : ℕ, 0 < m ∧ IsGenerated (lbPow L m) := by
  intro X O _ I _ Y s u a L hX hXs hL hspan hu hrange hgen
  have hc : ∀ x : X, ∃ i y, u i y = x := fun x => by
    have : ∃ i, a i ∉ (s x).asIdeal := by
      by_contra hne
      push Not at hne
      apply (s x).isPrime.ne_top
      rw [eq_top_iff, ← hspan]
      exact Ideal.span_le.2 (Set.range_subset_iff.2 hne)
    obtain ⟨i, hi⟩ := this
    have hx : x ∈ Set.range (u i) := by
      rw [hrange i]
      exact hi
    obtain ⟨y, hy⟩ := hx
    exact ⟨i, y, hy⟩
  have hpt : ∀ x : X, ∃ n, 1 ≤ n ∧ ∃ σ : (lbPow L n).Sec, x ∈ nonzeroLocus σ := fun x => by
    obtain ⟨i, y, rfl⟩ := hc x
    have hr : X.basicOpen ((s.appTop) ((Scheme.ΓSpecIso (CommRingCat.of O)).inv (a i))) = (u i).opensRange := by
      apply SetLike.coe_injective
      rw [basicOpen_eq O s (a i), ← hrange i]
      rfl
    obtain ⟨N, hN, hg⟩ := hgen i
    obtain ⟨t, ht⟩ := hg.exists_mem y
    exact ⟨N, hN, exists_sec_of_pull hL (u i) _ hr t y ht⟩
  choose n hn σ hσ using hpt
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top (fun x => nonzeroLocus (σ x)) hσ
  obtain ⟨N, hN, t, ht⟩ := exists_common_pow (fun x : T => n x) (fun x => hn x) (fun x => σ x)
  exact ⟨N, hN, isGenerated_of_finite t ((iSup_congr ht).trans hT)⟩

end GlobalTheory.BdDim.GenCover

end
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LBGerm GlobalTheory.AmpleOverBase

namespace GlobalTheory.GenNearExtend

theorem exists_sec_of_gen_near : ∀ (Z X : Scheme.{0}) (e : X ⟶ Z), IsOpenImmersion e → CompactSpace X →
    QuasiSeparatedSpace X → ∀ (M : LB Z), M.IsLB → ∀ (r : Γ(X, ⊤)) (O : Z.Opens),
    (∀ x ∈ X.basicOpen r, e x ∈ O) → ∀ t : LB.Gen (M.pull O.ι), t.IsGen →
    ∃ σ : LB.Sec (M.pull e), X.basicOpen r ≤ nonzeroLocus σ := by
  intro Z X e _ _ _ M hM r O hO t ht
  have hL : (M.pull e).IsLB := LB.isLB_pull hM e
  let f : (X.basicOpen r).toScheme ⟶ X := (X.basicOpen r).ι
  have hrange : Set.range (f ≫ e).base ⊆ Set.range O.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hO _ y.2
  let ψ : (X.basicOpen r).toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι (f ≫ e) hrange
  have hψ : ψ ≫ O.ι = f ≫ e := IsOpenImmersion.lift_fac _ _ _
  have hpt : ∀ y, O.ι (ψ y) = e (f y) := fun y => by
    rw [← Scheme.Hom.comp_apply, hψ, Scheme.Hom.comp_apply]
  let a : ChartPull (lbPow ((M.pull e).pull f) 1) (M.pull O.ι) ψ :=
    { idx := fun J _ => J PUnit.unit PUnit.unit PUnit.unit
      le := fun J y hy => by
        have h1 := mem_pull.1 (mem_pull.1 (mem_powChart.1 hy))
        show ψ y ∈ (M.pull O.ι).U _
        rw [mem_pull, hpt]
        exact h1
      g := fun y J J' hJ hJ' => by
        have h1 := mem_powChart.1 hJ
        have h2 := mem_powChart.1 hJ'
        have h1' : (𝟙 _ ≫ f) y ∈ (M.pull e).U (J PUnit.unit PUnit.unit) := mem_pull.1 h1
        have h2' : (𝟙 _ ≫ f) y ∈ (M.pull e).U (J' PUnit.unit PUnit.unit) := mem_pull.1 h2
        have h3 : ψ y ∈ (M.pull O.ι).U (fun _ => J PUnit.unit PUnit.unit PUnit.unit) := by
          rw [mem_pull, hpt]; exact mem_pull.1 (mem_pull.1 h1)
        have h4 : ψ y ∈ (M.pull O.ι).U (fun _ => J' PUnit.unit PUnit.unit PUnit.unit) := by
          rw [mem_pull, hpt]; exact mem_pull.1 (mem_pull.1 h2)
        refine (gm_lbPow_g 1 (𝟙 _) y J J' hJ hJ').trans ?_
        rw [pow_one, gm_pull_g ((M.pull e)) f (𝟙 _) y _ _ h1 h2, gm_pull_g M e (𝟙 _ ≫ f) y _ _ h1' h2',
          gm_pull_g M O.ι ψ y _ _ h3 h4, hψ, Category.id_comp] }
  let s0 : (M.pull O.ι).Sec := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  let t' := chartSec a s0
  have ht' : ∀ y, y ∈ nonzeroLocus t' := fun y => by
    obtain ⟨i, hi⟩ := exists_chart hM (e (f y))
    have hJ : y ∈ (lbPow ((M.pull e).pull f) 1).U (fun _ _ _ => i) :=
      mem_powChart.2 (mem_pull.2 (mem_pull.2 hi))
    rw [mem_nonzeroLocus_iff_isUnit t' hJ, gs_chartSec a s0 (𝟙 _) y _ hJ]
    have hm : (𝟙 _ ≫ ψ) y ∈ (M.pull O.ι).U (a.idx (fun _ _ _ => i)) := a.le _ hJ
    rw [gs_unit _ y _ hm]
    exact Units.isUnit _
  have hr : X.basicOpen r = f.opensRange := (Scheme.Opens.opensRange_ι _).symm
  have hs₀ : nonzeroLocus (secOfFn (M.pull e) r) = f.opensRange := (nonzeroLocus_secOfFn hL r).trans hr
  obtain ⟨T, hT, hTu⟩ := exists_push f (nonzeroLocus (secOfFn (M.pull e) r)) hs₀ t'
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul hL (secOfFn (M.pull e) r) T hT
  obtain ⟨u, hu⟩ := hN N le_rfl
  have key : ∀ (y' : (X.basicOpen r).toScheme) (J : PUnit → (M.pull e).ι), f y' ∈ powChart (M.pull e) J →
      (f y' ∈ nonzeroLocus u ↔ y' ∈ nonzeroLocus t') := fun y' J hJ => by
    have hs : f y' ∈ nonzeroLocus (secOfFn (M.pull e) r) := hs₀ ▸ ⟨y', rfl⟩
    have hy : f y' ∈ nonzeroLocus (secOfFn (M.pull e) r) ⊓ powChart (M.pull e) J := ⟨hs, hJ⟩
    have e' := congrArg (gs (𝟙 X) (f y') _) (hu J)
    rw [gs_res (𝟙 X) (f y') _ hy, gs_mul (𝟙 X) (f y') _ hy, gs_pow (𝟙 X) (f y') _ hy,
      gs_res (𝟙 X) (f y') _ hy] at e'
    rw [mem_nonzeroLocus_iff_powFn u hJ, e', IsUnit.mul_iff, hTu y' J hJ]
    exact and_iff_right (((mem_nonzeroLocus_iff_powFn _ hJ).1 hs).pow N)
  refine ⟨secOfPowOne (secCast (by omega) u), ?_⟩
  rw [nonzeroLocus_secOfPowOne, nonzeroLocus_secCast]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, f y = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨i, hi⟩ := exists_chart hL (f y)
  exact (key y (fun _ => i) (mem_powChart.2 hi)).2 (ht' y)

end GlobalTheory.GenNearExtend
end
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_basicOpen_of_nearGenerator : ∀ (Z X : Scheme.{0}) (e : X ⟶ Z), IsOpenImmersion e → CompactSpace X → QuasiSeparatedSpace X → ∀ (M : LB Z), M.IsLB → ∀ (r : Γ(X, ⊤)) (O : Z.Opens), (∀ x ∈ X.basicOpen r, e x ∈ O) → ∀ t : LB.Gen (M.pull O.ι), t.IsGen → ∃ σ : LB.Sec (M.pull e), X.basicOpen r ≤ nonzeroLocus σ := by
  atlas_forward_decl GlobalTheory.GenNearExtend.exists_sec_of_gen_near
end

section
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_sec_sum_nonzero :
    ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L),
      ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) →
        (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  intro X L κ _ r σ
  classical
  have hres : ∀ {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)),
      (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom a) =
        (X.presheaf.map (homOfLE (h2.trans h1)).op).hom a := by
    intro U V W h1 h2 a
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  let s : LB.Sec L :=
    { f := fun m => ∑ j, (X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j) * (σ j).f m
      compat := fun m n => by
        simp only [map_sum, map_mul, Finset.mul_sum, hres]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [(σ j).compat m n]
        ring }
  refine ⟨s, fun z i hri hσi hrj => ?_⟩
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hσi
  have hzm : z ∈ L.U m := X.basicOpen_le _ hm
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨m, ?_⟩
  rw [Scheme.mem_basicOpen X _ z hzm] at hm ⊢
  have hgerm : ∀ j, (X.presheaf.germ (L.U m) z hzm).hom
      ((X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j)) =
        (X.presheaf.germ ⊤ z trivial).hom (r j) := fun j =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  simp only [s, map_sum, map_mul, hgerm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hu : IsUnit ((X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m)) :=
    ((Scheme.mem_basicOpen_top X _ z).1 hri).mul hm
  have hmax : ∑ j ∈ Finset.univ.erase i, (X.presheaf.germ ⊤ z trivial).hom (r j) *
      (X.presheaf.germ (L.U m) z hzm).hom ((σ j).f m) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen_top]
    exact hrj j (Finset.ne_of_mem_erase hj)
  by_contra hn
  have : (X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    have h2 : _ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := (IsLocalRing.mem_maximalIdeal _).2 hn
    simpa using Ideal.sub_mem _ h2 hmax
  exact (IsLocalRing.mem_maximalIdeal _).1 this hu

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_where_single_coefficient : ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L), ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) → (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  atlas_forward_decl GlobalTheory.exists_sec_sum_nonzero
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem exists_sec_nonzero_on_fibre : ∀ (Y Y' Z' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ (p' : Z' ⟶ Y'), QuasiCompact p' → QuasiSeparated p' → ∀ (V : Y.Opens), IsAffineOpen V → ∀ y ∈ V, (∀ y₁ ∈ V, y ⤳ y₁ → y₁ = y) → ∀ (M : LB Z'), M.IsLB → (∀ x' : Y', k x' = y → ∃ W : Y'.Opens, x' ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) → ∃ s : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), ∀ z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, k (p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z)) = y → z ∈ nonzeroLocus s := by
  intro Y Y' Z' k hk p' hpc hps V hV y hy _ M hM hloc
  classical
  obtain ⟨hfin, hdisc⟩ := GlobalTheory.T.finite_fibre_and_eq_of_specializes_of_isFinite' Y Y' k hk y
  have hU : IsAffineOpen (k ⁻¹ᵁ V) := hV.preimage k
  let F : Finset Y' := hfin.toFinset
  have hF : ∀ a, a ∈ F ↔ k a = y := fun a => by simp [F]
  have hW : ∀ a : Y', ∃ W : Y'.Opens, (k a = y → a ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) := by
    intro a
    by_cases h : k a = y
    · obtain ⟨W, hW, t, ht⟩ := hloc a h
      exact ⟨W, fun _ => ⟨hW, t, ht⟩⟩
    · exact ⟨⊤, fun h' => absurd h' h⟩
  choose W hW using hW
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_separating_basicOpen_functions' Y' (k ⁻¹ᵁ V) hU F (fun a ha => by
      show k a ∈ V
      rw [(hF a).1 ha]; exact hy) (fun a ha b hb hab => hdisc a b ((hF a).1 ha) ((hF b).1 hb) hab)
    W (fun a ha => ((hW a) ((hF a).1 ha)).1)
  let q : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme ⟶ Y' := (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι ≫ p'
  have hq : (⊤ : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.Opens) ≤ q ⁻¹ᵁ (k ⁻¹ᵁ V) := by
    intro z _
    show p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z) ∈ k ⁻¹ᵁ V
    have h : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z ∈ p' ⁻¹ᵁ (k ⁻¹ᵁ V) := (Scheme.Opens.range_ι (p' ⁻¹ᵁ (k ⁻¹ᵁ V))).subset ⟨z, rfl⟩
    exact h
  let r : Y' → Γ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, ⊤) := fun a => (q.appLE (k ⁻¹ᵁ V) ⊤ hq).hom (f a)
  have hr : ∀ a (z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme), z ∈ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r a) ↔ q z ∈ Y'.basicOpen (f a) := by
    intro a z
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  haveI : CompactSpace (k ⁻¹ᵁ V).toScheme := isCompact_iff_compactSpace.1 hU.isCompact
  haveI : CompactSpace (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme := by
    have := hpc.isCompact_preimage _ (k ⁻¹ᵁ V).isOpen hU.isCompact
    exact isCompact_iff_compactSpace.1 this
  haveI : IsAffine (k ⁻¹ᵁ V).toScheme := hU
  haveI : QuasiSeparatedSpace (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme := quasiSeparatedSpace_of_quasiSeparated (p' ∣_ (k ⁻¹ᵁ V))
  have hσ : ∀ a : F, ∃ σ : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r a) ≤ nonzeroLocus σ := by
    rintro ⟨a, ha⟩
    obtain ⟨-, t, ht⟩ := hW a ((hF a).1 ha)
    exact GlobalTheory.T.exists_section_nonvanishing_basicOpen_of_nearGenerator Z' _ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι inferInstance ‹_› ‹_› M hM (r a) (p' ⁻¹ᵁ W a)
      (fun x hx => (hf a ha).2.1 ((hr a x).1 hx)) t ht
  choose σ hσ using hσ
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_nonvanishing_where_single_coefficient _ (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι) F (fun a => r a) σ
  refine ⟨s, fun z hz => ?_⟩
  have ha : q z ∈ F := (hF _).2 hz
  have h1 : z ∈ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r (q z)) := (hr _ z).2 (hf _ ha).1
  refine hs z ⟨q z, ha⟩ h1 (hσ _ h1) (fun j hj => ?_)
  rw [hr]
  exact (hf j.1 j.2).2.2 (q z) ha (fun h => hj (Subtype.ext h.symm))

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_over_closed_point_fibre : ∀ (Y Y' Z' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ (p' : Z' ⟶ Y'), QuasiCompact p' → QuasiSeparated p' → ∀ (V : Y.Opens), IsAffineOpen V → ∀ y ∈ V, (∀ y₁ ∈ V, y ⤳ y₁ → y₁ = y) → ∀ (M : LB Z'), M.IsLB → (∀ x' : Y', k x' = y → ∃ W : Y'.Opens, x' ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) → ∃ s : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), ∀ z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, k (p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z)) = y → z ∈ nonzeroLocus s := by
  atlas_forward_decl GlobalTheory.Mum.exists_sec_nonzero_on_fibre
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FlatGenDescent

variable {X X' : Scheme.{0}}

theorem isUnit_gs_iff {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f z U a) ↔ f z ∈ X.basicOpen a := by
  rw [gs_eq f z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

theorem exists_mul {M : LB X} (hM : M.IsLB) (u : LB.Sec M) (v : LB.Sec (AbLaw.pw M (-1))) :
    ∃ a : Γ(X, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : M.ι), r z ∈ M.U k →
      gs r z ⊤ a = gs r z (M.U k) (u.f k) * gs r z (M.U k) (v.f k) := by
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' M.U ⊤ (fun k => homOfLE le_top) hM.cover.ge
    (fun k => (show Γ(X, M.U k) from u.f k) * (show Γ(X, M.U k) from v.f k))
    (fun k l => fn_ext (V := M.U k ⊓ M.U l) fun y hy => by
      refine (gs_res (𝟙 X) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy _).symm)
      refine (gs_mul (𝟙 X) y _ hy.1 _ _).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy.2 _ _).symm)
      have h₁ := FlatSec.gs_sec_trans u (𝟙 X) y hy.1 hy.2
      have h₂ : gs (𝟙 X) y (M.U k) (v.f k) = (gm (𝟙 X) y (M.U k ⊓ M.U l) (M.g k l ^ (-1 : ℤ))).val *
          gs (𝟙 X) y (M.U l) (v.f l) := FlatSec.gs_sec_trans v (𝟙 X) y (k := k) (l := l) hy.1 hy.2
      rw [h₁, h₂, map_zpow, zpow_neg_one, _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul])
  refine ⟨a, fun Z r z k hk => ?_⟩
  exact (gs_res r z le_top hk a).symm.trans ((congrArg (gs r z (M.U k)) (ha k)).trans (gs_mul r z _ hk _ _))

def invSec (M : LB X) (π : X' ⟶ X) (t : LB.Gen (M.pull π)) (ht : t.IsGen) : LB.Sec ((AbLaw.pw M (-1)).pull π) :=
  genSec (M := (AbLaw.pw M (-1)).pull π) ⟨fun j => (t.s j)⁻¹⟩ fun i j => by
    have h := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at h
    refine h.trans (congrArg₂ (· * ·) ?_ rfl)
    show (∏ _k : PUnit, (res _ (pullU π _ (M.g _ _))) ^ (1 : ℤ))⁻¹ =
      ∏ _k : PUnit, (res _ (pullU π _ (M.g _ _ ^ (-1 : ℤ)))) ^ (1 : ℤ)
    rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, map_zpow, map_zpow, zpow_neg_one]

theorem exists_sec_of_flat {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Sp R) (π : X' ⟶ X) (f' : X' ⟶ Sp R') (H : IsPullback π f' f (spMap g))
    (M : LB X) (hM : M.IsLB) (t : LB.Gen (M.pull π)) (ht : t.IsGen) (m : Ideal Γ(X, ⊤)) (hm : m.IsMaximal) :
    ∃ u : LB.Sec M, ∀ z : X', (∀ a ∈ m, π z ∉ X.basicOpen a) → π z ∈ nonzeroLocus u := by
  classical
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H M hM (genSec t ht)
  obtain ⟨n', c', v, hv⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H _ (AbLaw.isLB_pw hM (-1))
    (invSec M π t ht)
  choose a ha using fun i j => exists_mul hM (u i) (v j)
  by_cases hne : ∃ i j, a i j ∉ m
  · obtain ⟨i, j, hij⟩ := hne
    refine ⟨u i, fun z hz => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hM (π z)
    obtain ⟨y, x, hx, e⟩ := hm.exists_inv hij
    have e' := congrArg (gs π z ⊤) e
    rw [gs_add π z ⊤ trivial, gs_mul π z ⊤ trivial, gs_eq π z ⊤ trivial 1, map_one, map_one] at e'
    have hxu : ¬ IsUnit (gs π z ⊤ x) := fun h => hz x hx ((isUnit_gs_iff π z ⊤ trivial x).1 h)
    have hu1 : IsUnit (gs π z ⊤ y * gs π z ⊤ (a i j)) :=
      (IsLocalRing.isUnit_or_isUnit_of_add_one e').resolve_right hxu
    have hu2 := isUnit_of_mul_isUnit_right hu1
    rw [ha i j X' π z k hk] at hu2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff π z _ hk _).1 (isUnit_of_mul_isUnit_left hu2)⟩
  · push_neg at hne
    refine ⟨⟨fun _ => 0, fun _ _ => by simp⟩, fun z hz => False.elim ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hM (π z)
    have hz' : z ∈ (M.pull π).U (fun _ => k) := mem_pull.2 hk
    have h₁ : (gm (𝟙 X') z ((M.pull π).U (fun _ => k)) (t.s fun _ => k)).val = _ :=
      (gs_unit (𝟙 X') z _ hz' _).symm.trans (hu z k hk)
    have h₂ : (gm (𝟙 X') z ((M.pull π).U (fun _ => k)) (t.s fun _ => k)⁻¹).val = _ :=
      (gs_unit (𝟙 X') z _ hz' _).symm.trans (hv z k hk)
    have h₃ := congrArg₂ (· * ·) h₁ h₂
    rw [map_inv, Units.mul_inv, Finset.sum_mul_sum] at h₃
    apply (IsLocalRing.maximalIdeal.isMaximal (X'.presheaf.stalk z)).ne_top
    rw [Ideal.eq_top_iff_one, h₃]
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    rw [_root_.mul_mul_mul_comm]
    refine Ideal.mul_mem_left _ _ ?_
    have h₄ : ¬ IsUnit (gs π z ⊤ (a i j)) := fun h => hz _ (hne i j) ((isUnit_gs_iff π z ⊤ trivial _).1 h)
    rw [ha i j X' π z k hk] at h₄
    exact h₄

theorem flat_of_basis {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R')
    (h : ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) : g.Flat := by
  let _ : Algebra R R' := g.toAlgebra
  have hb : Function.Bijective (Fintype.linearCombination R b) := by
    rw [Function.bijective_iff_existsUnique]
    intro r'
    refine (existsUnique_congr fun c => ?_).1 (h r')
    rw [Fintype.linearCombination_apply, eq_comm]
    rfl
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective _ hb).symm

theorem exists_sec_of_free : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R'), (∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) → ∀ (Z Z' : Scheme.{0}) (k' : Z' ⟶ Z) (f : Z ⟶ Sp R) (f' : Z' ⟶ Sp R'), IsPullback k' f' f (spMap g) → ∀ (O : Z.Opens), IsCompact (O : Set Z) → IsQuasiSeparated (O : Set Z) → ∀ (L : LB Z), L.IsLB → ∀ σ : LB.Gen ((L.pull k').pull (k' ⁻¹ᵁ O).ι), σ.IsGen → ∀ m : Ideal Γ(Z, O), m.IsMaximal → ∃ u : LB.Sec (L.pull O.ι), ∀ z : (k' ⁻¹ᵁ O).toScheme, (∀ a ∈ m, k' ((k' ⁻¹ᵁ O).ι z) ∉ Z.basicOpen a) → ∀ z₀ : O.toScheme, O.ι z₀ = k' ((k' ⁻¹ᵁ O).ι z) → z₀ ∈ nonzeroLocus u := by
  intro R R' _ _ g d b hb Z Z' k' f f' H O hO hO' L hL σ hσ m hm
  haveI : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hO
  haveI : QuasiSeparatedSpace O.toScheme := (isQuasiSeparated_iff_quasiSeparatedSpace _ O.isOpen).mp hO'
  have H' : IsPullback (k' ∣_ O) ((k' ⁻¹ᵁ O).ι ≫ f') (O.ι ≫ f) (spMap g) :=
    (isPullback_morphismRestrict k' O).paste_vert H
  obtain ⟨t₁, h₁⟩ := gen_chartPull (chartPullIn L (fun _ : PUnit => k') (fun _ => 1) (k' ⁻¹ᵁ O).ι) σ hσ
  obtain ⟨t, ht⟩ := gen_chartPull (chartPullOut L (fun _ : PUnit => O.ι) (fun _ => 1) (k' ∣_ O) _
    fun _ => (morphismRestrict_ι k' O).symm) t₁ h₁
  let e : Γ(O.toScheme, ⊤) ≃+* Γ(Z, O) := O.topIso.commRingCatIsoToRingEquiv
  haveI := hm
  obtain ⟨u, hu⟩ := exists_sec_of_flat g (flat_of_basis g d b hb) (O.ι ≫ f) (k' ∣_ O) _ H' (L.pull O.ι)
    (LB.isLB_pull hL _) t ht (m.comap e) (Ideal.comap_isMaximal_of_surjective e e.surjective)
  refine ⟨u, fun z hz z₀ hz₀ => ?_⟩
  have hc : O.ι ((k' ∣_ O) z) = k' ((k' ⁻¹ᵁ O).ι z) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  obtain rfl : z₀ = (k' ∣_ O) z := O.ι.injective (hz₀.trans hc.symm)
  refine hu z fun a ha h => hz (e a) ha ?_
  rw [← hc]
  have := O.ι_image_basicOpen_topIso_inv (e a)
  rw [← this]
  exact ⟨_, (show _ ∈ O.toScheme.basicOpen (O.topIso.inv.hom (e a)) from (e.symm_apply_apply a).symm ▸ h), rfl⟩

end GlobalTheory.FlatGenDescent
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_of_finite_free_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R'), (∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) → ∀ (Z Z' : Scheme.{0}) (k' : Z' ⟶ Z) (f : Z ⟶ Sp R) (f' : Z' ⟶ Sp R'), IsPullback k' f' f (spMap g) → ∀ (O : Z.Opens), IsCompact (O : Set Z) → IsQuasiSeparated (O : Set Z) → ∀ (L : LB Z), L.IsLB → ∀ σ : LB.Gen ((L.pull k').pull (k' ⁻¹ᵁ O).ι), σ.IsGen → ∀ m : Ideal Γ(Z, O), m.IsMaximal → ∃ u : LB.Sec (L.pull O.ι), ∀ z : (k' ⁻¹ᵁ O).toScheme, (∀ a ∈ m, k' ((k' ⁻¹ᵁ O).ι z) ∉ Z.basicOpen a) → ∀ z₀ : O.toScheme, O.ι z₀ = k' ((k' ⁻¹ᵁ O).ι z) → z₀ ∈ nonzeroLocus u := by
  atlas_forward_decl GlobalTheory.FlatGenDescent.exists_sec_of_free
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_gen_near_of_finFlat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsLocallyNoetherian Y → (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ x : Y', ∃ V : Y'.Opens, x ∈ V ∧ ∃ t : LB.Gen ((L'.pull k').pull (p' ⁻¹ᵁ V).ι), t.IsGen) → ∀ x : Y, ∃ V : Y.Opens, x ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hflat Z Y Z' Y' p p' y y' k k' hk hk' hp hY hbij L hL hloc x
  haveI : IsNoetherianRing R := hR.1
  obtain ⟨hkf, hqc, hqs, hsurj, hcl, hclp, hO, d, b, hb⟩ :=
    GlobalTheory.T.finite_flat_local_baseChange_of_proper_properties R R' ρ hfin.2.1 hfin.2.2 hflat Z Y Z' Y' p p' y y' k k' hk hk' hp
  obtain ⟨V, hV, y₀, hy₀, hxy, hE⟩ := GlobalTheory.T.exists_specialization_closed_in_affine_neighbourhood Y x
  obtain ⟨hclV, -⟩ := hE V le_rfl hV hy₀
  have hL' : (L.pull k').IsLB := LB.isLB_pull hL _
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_nonvanishing_over_closed_point_fibre Y Y' Z' k hkf p' hqc hqs V hV y₀ hy₀ hclV (L.pull k') hL' (fun x' _ => hloc x')
  obtain ⟨V₁, hy₁, hV₁V, hV₁⟩ := GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap Z' Y (p' ≫ k) hcl (L.pull k') V s y₀ hy₀ hs
  obtain ⟨f, hf1, hf2⟩ := hV.exists_basicOpen_le ⟨y₀, hy₁⟩ hy₀
  have hV₂V : Y.basicOpen f ≤ V := Y.basicOpen_le f
  have hV₂ : IsAffineOpen (Y.basicOpen f) := hV.basicOpen f
  obtain ⟨-, M, hM, hMiff⟩ := hE (Y.basicOpen f) hV₂V hV₂ hf2
  have hcomm : ∀ z : Z', p (k' z) = k (p' z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk'.w]
  have hle : k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f) ≤ p' ⁻¹ᵁ (k ⁻¹ᵁ V) := fun z hz => by
    show k (p' z) ∈ V
    rw [← hcomm]
    exact hV₂V hz
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section Z' (L.pull k') hL' _ _ hle s (fun z₀ hz₀ => hV₁ z₀ (by
    rw [Scheme.Hom.comp_apply, ← hcomm]
    exact hf1 hz₀))
  have hsurjp : Function.Surjective (p.app (Y.basicOpen f)).hom := (hbij _).2
  let e := RingEquiv.ofBijective (p.app (Y.basicOpen f)).hom (hbij _)
  haveI hm : (Ideal.comap e.symm.toRingHom M).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  obtain ⟨hOc, hOq⟩ := hO _ hV₂
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_nonzero_section_of_finite_free_baseChange R R' ρ d b hb Z Z' k' (p ≫ y) (p' ≫ y') (hk'.paste_vert hk) (p ⁻¹ᵁ Y.basicOpen f) hOc hOq
    L hL σ hσ _ hm
  have hfib : ∀ z₀ : (p ⁻¹ᵁ Y.basicOpen f).toScheme, p ((p ⁻¹ᵁ Y.basicOpen f).ι z₀) = y₀ → z₀ ∈ nonzeroLocus u := by
    intro z₀ hz₀
    obtain ⟨z', hz'⟩ := hsurj ((p ⁻¹ᵁ Y.basicOpen f).ι z₀)
    have hz'O : z' ∈ k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f) := by
      show k' z' ∈ p ⁻¹ᵁ Y.basicOpen f
      rw [hz']
      first | exact z₀.2 | simpa using z₀.2 | exact (Scheme.Opens.range_ι _).subset ⟨z₀, rfl⟩
    obtain ⟨w, hw⟩ : z' ∈ Set.range (k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f)).ι.base := by
      rw [Scheme.Opens.range_ι]; exact hz'O
    refine hu w (fun a ha => ?_) z₀ (by rw [← hz']; exact congrArg k'.base hw |>.symm)
    have ha₀ : e.symm a ∈ M := ha
    have ea : a = p.app (Y.basicOpen f) (e.symm a) := (e.apply_symm_apply a).symm
    intro hmem
    rw [ea, ← Scheme.preimage_basicOpen] at hmem
    have : k' ((k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f)).ι w) = (p ⁻¹ᵁ Y.basicOpen f).ι z₀ := by
      rw [← hz']; exact congrArg k'.base hw
    rw [this] at hmem
    have hmem' : p ((p ⁻¹ᵁ Y.basicOpen f).ι z₀) ∈ Y.basicOpen (e.symm a) := hmem
    rw [hz₀] at hmem'
    exact (hMiff _).1 ha₀ hmem'
  obtain ⟨V₃, hy₃, hV₃, hV₃u⟩ := GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap Z Y p hclp L _ u y₀ hf2 hfib
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section Z L hL (p ⁻¹ᵁ V₃) (p ⁻¹ᵁ Y.basicOpen f) (fun z hz => hV₃ hz) u
    (fun z hz => hV₃u z hz)
  exact ⟨V₃, hxy.mem_open V₃.isOpen hy₃, t, ht⟩

end GlobalTheory.Mum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_near_fibres_of_finiteFlat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsLocallyNoetherian Y → (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ x : Y', ∃ V : Y'.Opens, x ∈ V ∧ ∃ t : LB.Gen ((L'.pull k').pull (p' ⁻¹ᵁ V).ι), t.IsGen) → ∀ x : Y, ∃ V : Y.Opens, x ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen := by
  atlas_forward_decl GlobalTheory.Mum.exists_gen_near_of_finFlat
end

section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ClosedPt

theorem gen_pull_pull_of {X Y Z : Scheme.{0}} (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (c : Z ⟶ X) (hc : c = b ≫ a)
    (h : ∃ t : LB.Gen (L.pull c), t.IsGen) : ∃ t : LB.Gen ((L.pull a).pull b), t.IsGen := by
  subst hc
  refine Pdiv.PullbackComparison.exists_gen_transfer (L := L.pull (b ≫ a)) (L' := (L.pull a).pull b)
    (fun j _ => j PUnit.unit PUnit.unit) (fun j z hz => ?_) (fun i j y hy => ?_) h
  · exact (Pdiv.PullbackComparison.mem_wchart_pu L (b ≫ a) _ z).2
      ((Pdiv.PullbackComparison.mem_wchart_pu L a _ _).1 ((Pdiv.PullbackComparison.mem_wchart_pu (L.pull a) b j z).1 hz))
  · have hy' : y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) :=
      Pdiv.PullbackComparison.pull_inf_le L a _ _ (Pdiv.PullbackComparison.pull_inf_le (L.pull a) b i j hy)
    exact (Pdiv.PullbackComparison.germ_pull_pull L a b i j y hy hy').trans
      (Pdiv.PullbackComparison.germ_pull L (b ≫ a) (fun _ => i PUnit.unit PUnit.unit) (fun _ => j PUnit.unit PUnit.unit) y _ hy').symm

theorem gen_of_pull_pull {X Y Z : Scheme.{0}} (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (c : Z ⟶ X) (hc : c = b ≫ a)
    (h : ∃ t : LB.Gen ((L.pull a).pull b), t.IsGen) : ∃ t : LB.Gen (L.pull c), t.IsGen := by
  subst hc
  have hU : ∀ (j : PUnit → L.ι), (L.pull (b ≫ a)).U j ≤ ((L.pull a).pull b).U (fun _ => j) := fun j z hz =>
    (Pdiv.PullbackComparison.mem_wchart_pu (L.pull a) b _ z).2 ((Pdiv.PullbackComparison.mem_wchart_pu L a _ _).2
      ((Pdiv.PullbackComparison.mem_wchart_pu L (b ≫ a) j z).1 hz))
  refine Pdiv.PullbackComparison.exists_gen_transfer (L' := L.pull (b ≫ a)) (L := (L.pull a).pull b)
    (fun j _ => j) hU (fun i j y hy => ?_) h
  have hy' : y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) := Pdiv.PullbackComparison.pull_inf_le L (b ≫ a) _ _ hy
  exact (Pdiv.PullbackComparison.germ_pull L (b ≫ a) i j y hy hy').trans
    (Pdiv.PullbackComparison.germ_pull_pull L a b (fun _ => i) (fun _ => j) y _ hy').symm

theorem gen_comp {X Y Z : Scheme.{0}} (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (c : Z ⟶ X) (hc : c = b ≫ a)
    (h : ∃ t : LB.Gen (L.pull a), t.IsGen) : ∃ t : LB.Gen (L.pull c), t.IsGen := by
  subst hc
  obtain ⟨t, ht⟩ := h
  exact ⟨LB.pullGen L (fun _ : PUnit => a) (fun _ => 1) t b, DVR.pullGen_isGen L (fun _ : PUnit => a) (fun _ => 1) t ht b⟩

theorem isFinite_fromSpec {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f] (y : X) (hy : IsClosed ({y} : Set X))
    (hs : IsClosed ({f y} : Set S)) : IsFinite (X.fromSpecResidueField y ≫ f) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hy
  have := isClosed_singleton_iff_isClosedImmersion.1 hs
  have e := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f y
  have h₁ : LocallyOfFiniteType (Spec.map (f.residueFieldMap y) ≫ S.fromSpecResidueField (f y)) := by
    rw [e]; infer_instance
  have h₂ : LocallyOfFiniteType (Spec.map (f.residueFieldMap y)) :=
    locallyOfFiniteType_of_comp _ (S.fromSpecResidueField (f y))
  have h₃ : IsFinite (Spec.map (f.residueFieldMap y)) := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 h₂
  rw [← e]; infer_instance

theorem exists_open_good {G X S : Scheme.{0}} (g : G ⟶ S) (x : X ⟶ S) [GeometricallyIrreducible x] (y : G)
    [IsFinite (G.fromSpecResidueField y ≫ g)] {K : Type} (l : List K) (W : K → (pullback g x).Opens)
    (hW : ∀ i ∈ l, ∃ q ∈ W i, pullback.fst g x q = y) :
    ∃ N : X.Opens, (∃ u ∈ N, x u = g y) ∧
      ∀ q : (pullback g x : Scheme.{0}), pullback.fst g x q = y → pullback.snd g x q ∈ N → ∀ i ∈ l, q ∈ W i := by
  let j := pullback.fst (pullback.fst g x) (G.fromSpecResidueField y)
  have sq : IsPullback (j ≫ pullback.snd g x) (pullback.snd (pullback.fst g x) (G.fromSpecResidueField y)) x
      (G.fromSpecResidueField y ≫ g) :=
    (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback g x).flip
  have hfin : IsFinite (j ≫ pullback.snd g x) := MorphismProperty.of_isPullback sq.flip ‹_›
  have hirr : IrreducibleSpace (pullback (pullback.fst g x) (G.fromSpecResidueField y) : Scheme.{0}) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := pullback.fst g x) _ _ _ (IsPullback.of_hasPullback _ _)
  have hr : ∀ q, pullback.fst g x q = y → ∃ p, j p = q := fun q hq => by
    have : q ∈ Set.range j := by
      rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]; exact hq
    exact this
  let ξ := genericPoint (pullback (pullback.fst g x) (G.fromSpecResidueField y) : Scheme.{0})
  have hξ : ∀ i ∈ l, j ξ ∈ W i := fun i hi => by
    obtain ⟨q, hq, hqy⟩ := hW i hi
    obtain ⟨p, rfl⟩ := hr q hqy
    exact ((genericPoint_specializes p).map j.continuous).mem_open (W i).isOpen hq
  have hU : IsOpen {p | ∀ i ∈ l, j p ∈ W i} := by
    have : {p | ∀ i ∈ l, j p ∈ W i} = ⋂ i ∈ {i | i ∈ l}, j ⁻¹' (W i) := by ext; simp
    rw [this]
    exact (List.finite_toSet l).isOpen_biInter fun i _ => (W i).isOpen.preimage j.continuous
  have hB := (j ≫ pullback.snd g x).isClosedMap _ hU.isClosed_compl
  refine ⟨⟨_, hB.isOpen_compl⟩, ⟨(j ≫ pullback.snd g x) ξ, ?_, ?_⟩, ?_⟩
  · rintro ⟨p, hp, hpξ⟩
    have hd := (j ≫ pullback.snd g x).isDiscrete_preimage_singleton ((j ≫ pullback.snd g x) ξ)
    have : ξ = p := by
      have := hd.to_subtype
      have hs : (⟨ξ, rfl⟩ : (j ≫ pullback.snd g x) ⁻¹' {(j ≫ pullback.snd g x) ξ}) ⤳ ⟨p, hpξ⟩ :=
        Topology.IsInducing.subtypeVal.specializes_iff.1 (genericPoint_specializes p)
      exact congrArg Subtype.val hs.eq
    exact hp (this ▸ hξ)
  · rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  · intro q hq hN
    obtain ⟨p, rfl⟩ := hr q hq
    by_contra h
    exact hN ⟨p, h, Scheme.Hom.comp_apply _ _ _⟩

def ten {S : Scheme.{0}} (G : Over S) [GrpObj G] : List (G ⊗ G ⊗ G ⊗ G ⟶ G) :=
  cubeTen (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _ ≫ snd _ _)

theorem ten_solve {S : Scheme.{0}} (G : Over S) [GrpObj G] {T : Over S} (y g : T ⟶ G) :
    ∀ f ∈ ten G, ∃ u : T ⟶ G ⊗ G ⊗ G, lift y u ≫ f = g := by
  intro f hf
  simp only [ten, cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨lift (y⁻¹ * g) (lift 1 1), by simp [MonObj.comp_mul]⟩
  · exact ⟨lift (g⁻¹ * y) (lift 1 1), by simp [MonObj.comp_mul, GrpObj.comp_inv]⟩
  · exact ⟨lift g (lift 1 1), by simp⟩
  · exact ⟨lift g⁻¹ (lift 1 1), by simp [GrpObj.comp_inv]⟩
  · exact ⟨lift 1 (lift (y⁻¹ * g) 1), by simp [MonObj.comp_mul]⟩
  · exact ⟨lift 1 (lift 1 (y⁻¹ * g)), by simp [MonObj.comp_mul]⟩
  · exact ⟨lift 1 (lift (g⁻¹ * y) 1), by simp [MonObj.comp_mul, GrpObj.comp_inv]⟩
  · exact ⟨lift 1 (lift g 1), by simp⟩
  · exact ⟨lift 1 (lift 1 g), by simp⟩
  · exact ⟨lift 1 (lift g⁻¹ 1), by simp [MonObj.comp_mul, GrpObj.comp_inv]⟩

theorem ten_meets {S : Scheme.{0}} (G : Over S) [GrpObj G] (y g : G.left) (h : G.hom y = G.hom g) :
    ∀ f ∈ ten G, ∃ q : (pullback G.hom (G ⊗ G ⊗ G).hom : Scheme.{0}),
      f.left q = g ∧ pullback.fst G.hom (G ⊗ G ⊗ G).hom q = y := by
  intro f hf
  obtain ⟨z, hy, hg⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) y g h
  obtain ⟨u, hu⟩ := ten_solve G (fst G G) (snd G G) f hf
  refine ⟨(lift (fst G G) u).left z, ?_, ?_⟩
  · exact (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun φ => φ.left z) hu).trans hg)
  · exact (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun φ => φ.left z) (lift_fst (fst G G) u)).trans hy)

theorem gen_of_ten {T S : Scheme.{0}} (π : S ⟶ T) (G : Over T) [GrpObj G] (G' : Over S) [GrpObj G'] [IsCommMonObj G']
    (β : G'.left ⟶ G.left) (hpb : IsGrpPullback G' G π β) (P : GlobalTheory.UU.CP G') (θ : P.L.L.Sec) {Z : Scheme.{0}}
    (k : Z ⟶ G'.left) (ζ : Z ⟶ (G ⊗ G ⊗ G ⊗ G).left) (hζ : ζ ≫ (fst G _).left = k ≫ β)
    (h : ∀ f ∈ ten G, ∀ z, f.left (ζ z) ∈ farSet β θ) : ∃ t : LB.Gen (P.L.L.pull k), t.IsGen := by
  have hw : ζ ≫ (G ⊗ G ⊗ G ⊗ G).hom = (Over.mk (k ≫ G'.hom)).hom ≫ π := by
    rw [← Over.w (fst G _), ← Category.assoc, hζ, Category.assoc, hpb.1.w]; exact (Category.assoc _ _ _).symm
  obtain ⟨hl, hm⟩ := GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv T S π G G' β hpb (Over.mk (k ≫ G'.hom)) (G ⊗ G ⊗ G ⊗ G) ζ hw
  obtain ⟨a, ha⟩ := hl (snd _ _ ≫ fst _ _)
  obtain ⟨b, hb⟩ := hl (snd _ _ ≫ snd _ _ ≫ fst _ _)
  obtain ⟨c, hc⟩ := hl (snd _ _ ≫ snd _ _ ≫ snd _ _)
  let x : Over.mk (k ≫ G'.hom) ⟶ G' := Over.homMk k rfl
  have hx : x.left ≫ β = ζ ≫ (fst G _).left := hζ.symm
  have mu := fun u v u' v' h₁ h₂ => (hm u v u' v' h₁ h₂).1
  have iv := fun u u' h₁ => (hm u u u' u' h₁ h₁).2
  have key : ∀ f' ∈ cubeTen x a b c, ∃ f ∈ ten G, f'.left ≫ β = ζ ≫ f.left := by
    intro f hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [ten, cubeTen], mu _ _ _ _ hx ha⟩
    · exact ⟨_, by simp [ten, cubeTen], mu _ _ _ _ hx (iv _ _ ha)⟩
    · exact ⟨_, by simp [ten, cubeTen], ha⟩
    · exact ⟨_, by simp [ten, cubeTen], iv _ _ ha⟩
    · exact ⟨_, by simp [ten, cubeTen], mu _ _ _ _ hx hb⟩
    · exact ⟨_, by simp [ten, cubeTen], mu _ _ _ _ hx hc⟩
    · exact ⟨_, by simp [ten, cubeTen], mu _ _ _ _ hx (iv _ _ (mu _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [ten, cubeTen], hb⟩
    · exact ⟨_, by simp [ten, cubeTen], hc⟩
    · exact ⟨_, by simp [ten, cubeTen], iv _ _ (mu _ _ _ _ hb hc)⟩
  have hg := GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points S G' P θ (Over.mk (k ≫ G'.hom)) x a b c ⊤ fun f' hf' z _ => by
    obtain ⟨f, hf, e⟩ := key f' hf'
    refine h f hf z _ ?_
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun φ => φ z) e).trans (Scheme.Hom.comp_apply _ _ _))
  exact gen_comp _ _ Z.topIso.inv k (by simp [x]) hg

theorem exists_gen_near_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR M G' _ _ hG' P' G _ _ β hG hpb θ O hO hθ y hyc hy
  have hN : IsNoetherianRing R := hR.1
  have hI : IsIntegrallyClosed R := hR.2.2.1
  have := hG.smooth
  have := M.proper
  have hβ : IsProper β := MorphismProperty.of_isPullback hpb.1.flip M.proper
  have hgi : GeometricallyIrreducible G.hom :=
    ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun Ω _ s => GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint _ G hG Ω s⟩
  have s₂ : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have i₂ : GeometricallyIrreducible (G ⊗ G).hom := GeometricallyIrreducible.comp (pullback.fst G.hom G.hom) G.hom
  have s₃ : Smooth (G ⊗ G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom (G ⊗ G).hom ≫ G.hom))
  have i₃ : GeometricallyIrreducible (G ⊗ G ⊗ G).hom :=
    GeometricallyIrreducible.comp (pullback.fst G.hom (G ⊗ G).hom) G.hom
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  obtain ⟨g, hgO, hg⟩ := hO
  have hgO' : g ∈ O' := fun g' e => by
    subst e
    exact TopologicalSpace.Opens.mem_iSup.2 (hθ g' hgO hg)
  have hfin : IsFinite (G.left.fromSpecResidueField y ≫ G.hom) :=
    isFinite_fromSpec G.hom y hyc (by rw [hy]; exact isClosed_singleton_closedPoint R)
  obtain ⟨N, hN₁, hN₂⟩ := exists_open_good G.hom (G ⊗ G ⊗ G).hom y (ten G) (fun f => f.left ⁻¹ᵁ O') fun f hf => by
    obtain ⟨q, h₁, h₂⟩ := ten_meets G y g (hy.trans hg.symm) f hf
    exact ⟨q, show f.left q ∈ O' from h₁ ▸ hgO', h₂⟩
  rw [hy] at hN₁
  obtain ⟨R', _, _, _, ρ, t, hρ, het, ht, htN⟩ := GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre R hR (G ⊗ G ⊗ G) s₃ N hN₁
  have hρf : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff (CommRingCat.ofHom ρ)).2 hρ.2.2
  have hflat : ρ.Flat := by
    algebraize [ρ]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  let m : pullback G.hom (spMap ρ) ⟶ pullback G.hom (G ⊗ G ⊗ G).hom :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t) (by rw [Category.assoc, ht]; exact pullback.condition)
  have m₁ : m ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have m₂ : m ≫ pullback.snd _ _ = pullback.snd _ _ ≫ t := pullback.lift_snd _ _ _
  have hU : IsOpen {p | ∀ f ∈ ten G, f.left (m p) ∈ O'} := by
    have : {p | ∀ f ∈ ten G, f.left (m p) ∈ O'} = ⋂ f ∈ {f | f ∈ ten G}, m ⁻¹' (f.left ⁻¹' O') := by ext; simp
    rw [this]
    exact (List.finite_toSet _).isOpen_biInter fun f _ => (O'.isOpen.preimage f.left.continuous).preimage m.continuous
  let V : G.left.Opens := ⟨_, ((pullback.fst G.hom (spMap ρ)).isClosedMap _ hU.isClosed_compl).isOpen_compl⟩
  have hyV : y ∈ V := by
    rintro ⟨p, hp, hpy⟩
    refine hp (hN₂ (m p) ?_ ?_)
    · rw [← Scheme.Hom.comp_apply, m₁, hpy]
    · rw [← Scheme.Hom.comp_apply, m₂, Scheme.Hom.comp_apply]
      exact htN ⟨_, rfl⟩
  let k := pullback.fst (V.ι ≫ G.hom) (spMap ρ)
  let n : pullback (V.ι ≫ G.hom) (spMap ρ) ⟶ pullback G.hom (spMap ρ) :=
    pullback.lift (k ≫ V.ι) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  have n₁ : n ≫ pullback.fst _ _ = k ≫ V.ι := pullback.lift_fst _ _ _
  have hn : ∀ p, ∀ f ∈ ten G, f.left (m (n p)) ∈ O' := fun p => by
    by_contra h
    have : V.ι (k p) ∈ V := (k p).2
    refine this ⟨n p, h, ?_⟩
    rw [← Scheme.Hom.comp_apply, n₁, Scheme.Hom.comp_apply]
  have hgen := gen_of_ten M.π G G' β hpb P' θ (pullback.fst (β ∣_ V) k ≫ (β ⁻¹ᵁ V).ι)
    (pullback.snd (β ∣_ V) k ≫ n ≫ m) (by
      change (pullback.snd (β ∣_ V) k ≫ n ≫ m) ≫ pullback.fst G.hom (G ⊗ G ⊗ G).hom = _
      rw [Category.assoc, Category.assoc, m₁, n₁, ← pullback.condition_assoc, morphismRestrict_ι, Category.assoc])
    fun f hf z => by
      have := hn (pullback.snd (β ∣_ V) k z) f hf
      rw [← Scheme.Hom.comp_apply n m, ← Scheme.Hom.comp_apply (pullback.snd (β ∣_ V) k)] at this
      exact this
  have sq : IsPullback (β ∣_ V) ((β ⁻¹ᵁ V).ι ≫ G'.hom) (V.ι ≫ G.hom) M.π :=
    (isPullback_morphismRestrict β V).paste_vert hpb.1
  have hnoeth : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨V₁, hV₁, hgen₁⟩ := GlobalTheory.T.exists_generator_near_fibres_of_finiteFlat R hR R' ρ hρ hflat _ _ _ _ (β ∣_ V) (pullback.snd (β ∣_ V) k) (V.ι ≫ G.hom)
    (pullback.snd _ _) k (pullback.fst (β ∣_ V) k) (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
    inferInstance inferInstance
    (app_bijective_of_flat_baseChange R M.S _ _ M.π (V.ι ≫ G.hom) (β ∣_ V) _ inferInstance inferInstance
      (Modif.appTop_bijective_surjective R M).1 inferInstance sq)
    (P'.L.L.pull (β ⁻¹ᵁ V).ι) (pull_isLB P'.L.isLB _)
    (fun _ => ⟨⊤, trivial, gen_pull_pull_of _ _ _ _ rfl (gen_comp _ _ _ _ rfl (gen_pull_pull_of _ _ _ _ rfl hgen))⟩)
    ⟨y, hyV⟩
  refine ⟨V.ι ''ᵁ V₁, ⟨⟨y, hyV⟩, hV₁, rfl⟩, ?_⟩
  have hr : Set.range (β ⁻¹ᵁ (V.ι ''ᵁ V₁)).ι ⊆ Set.range (((β ∣_ V) ⁻¹ᵁ V₁).ι ≫ (β ⁻¹ᵁ V).ι) := by
    rintro _ ⟨⟨z, v, hv, hz⟩, rfl⟩
    have hz' : v.1 = β z := hz
    have hzV : z ∈ β ⁻¹ᵁ V := show β z ∈ V from hz' ▸ v.2
    refine ⟨⟨⟨z, hzV⟩, ?_⟩, rfl⟩
    have : (β ∣_ V) ⟨z, hzV⟩ = v := Subtype.ext ((morphismRestrict_base_coe β V ⟨z, hzV⟩).trans hz'.symm)
    exact show (β ∣_ V) ⟨z, hzV⟩ ∈ V₁ from this ▸ hv
  exact gen_comp _ _ (IsOpenImmersion.lift _ _ hr) _ (IsOpenImmersion.lift_fac _ _ hr).symm
    (gen_of_pull_pull _ _ _ _ rfl hgen₁)

end GlobalTheory.Mum.ClosedPt
end
end
