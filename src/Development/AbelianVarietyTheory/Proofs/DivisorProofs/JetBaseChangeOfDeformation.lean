import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFiltrationSpannedCorrespondence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageCorrespondence

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatJet

variable {R : Type} [CommRing R] (σ : R →+* ℂ) {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (J' : JetRing ℂ I n)

def coeffMap (x : J.B) : J'.B := J'.b.repr.symm (Finsupp.mapRange σ σ.map_zero (J.b.repr x))

variable {σ J J'}

theorem coeffMap_repr (x : J.B) (ν : Idx I n) : J'.b.repr (coeffMap σ J J' x) ν = σ (J.b.repr x ν) := by
  simp [coeffMap]

theorem coeffMap_add (x y : J.B) : coeffMap σ J J' (x + y) = coeffMap σ J J' x + coeffMap σ J J' y := by
  refine J'.b.ext_elem fun ν => ?_
  simp [coeffMap_repr]

theorem coeffMap_zero : coeffMap σ J J' 0 = 0 := by
  refine J'.b.ext_elem fun ν => ?_
  simp [coeffMap_repr]

theorem coeffMap_smul (r : R) (x : J.B) : coeffMap σ J J' (r • x) = σ r • coeffMap σ J J' x := by
  refine J'.b.ext_elem fun ν => ?_
  simp [coeffMap_repr]

theorem coeffMap_nsmul (k : ℕ) (x : J.B) : coeffMap σ J J' (k • x) = k • coeffMap σ J J' x := by
  rw [← Nat.cast_smul_eq_nsmul R k x, coeffMap_smul, map_natCast, Nat.cast_smul_eq_nsmul]

theorem coeffMap_basis (ν : Idx I n) : coeffMap σ J J' (J.b ν) = J'.b ν := by
  refine J'.b.ext_elem fun ρ => ?_
  rw [coeffMap_repr, J.b.repr_self, J'.b.repr_self, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

theorem coeffMap_basis_mul (ν ν' : Idx I n) :
    coeffMap σ J J' (J.b ν * J.b ν') = J'.b ν * J'.b ν' := by
  rw [JetRing.mul J, JetRing.mul J']
  split_ifs
  · rw [coeffMap_nsmul, coeffMap_basis]
  · exact coeffMap_zero

theorem coeffMap_one : coeffMap σ J J' 1 = 1 := by
  rw [← J.one, coeffMap_basis, J'.one]

theorem coeffMap_mul (x y : J.B) : coeffMap σ J J' (x * y) = coeffMap σ J J' x * coeffMap σ J J' y := by
  have hx : x ∈ Submodule.span R (Set.range J.b) := J.b.mem_span x
  have hy : y ∈ Submodule.span R (Set.range J.b) := J.b.mem_span y
  induction hx using Submodule.span_induction generalizing y with
  | mem a ha =>
    obtain ⟨ν, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨ν', rfl⟩ := hc
      rw [coeffMap_basis_mul, coeffMap_basis, coeffMap_basis]
    | zero => rw [mul_zero, coeffMap_zero, mul_zero]
    | add u v _ _ hu hv => rw [mul_add, coeffMap_add, coeffMap_add, hu, hv, mul_add]
    | smul r u _ hu => rw [mul_smul_comm, coeffMap_smul, coeffMap_smul, hu, mul_smul_comm]
  | zero => rw [zero_mul, coeffMap_zero, zero_mul]
  | add u v _ _ hu hv => rw [add_mul, coeffMap_add, coeffMap_add, hu y hy, hv y hy, add_mul]
  | smul r u _ hu => rw [smul_mul_assoc, coeffMap_smul, coeffMap_smul, hu y hy, smul_mul_assoc]

variable (σ J J')

def coeffHom : J.B →+* J'.B where
  toFun := coeffMap σ J J'
  map_one' := coeffMap_one
  map_mul' := coeffMap_mul
  map_zero' := coeffMap_zero
  map_add' := coeffMap_add

theorem coeffHom_isDPMorphism : IsDPMorphism J.κ J'.κ (coeffHom σ J J') := by
  have hker : ∀ a ∈ RingHom.ker J.π, coeffHom σ J J' a ∈ RingHom.ker J'.π := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [J'.π_eq, coeffHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeffMap_repr, ← J.π_eq, ha, map_zero]
  refine ⟨?_, fun {k} a ha => ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    exact fun a ha => hker a ha
  · have hu : IsUnit ((k.factorial : ℕ) : J'.B) := by
      have : ((k.factorial : ℕ) : J'.B) = algebraMap ℂ J'.B (k.factorial : ℂ) := by simp
      rw [this]
      exact (IsUnit.mk0 _ (by exact_mod_cast k.factorial_ne_zero)).map _
    refine hu.mul_left_cancel ?_
    rw [J'.κ.factorial_mul_dpow_eq_pow (hker a ha), ← map_natCast (coeffHom σ J J'), ← map_mul,
      J.κ.factorial_mul_dpow_eq_pow ha, map_pow]

theorem exists_coeffHom : ∃ τ : J.B →+* J'.B, (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) ∧ IsDPMorphism J.κ J'.κ τ :=
  ⟨coeffHom σ J J', fun x ν => coeffMap_repr x ν, coeffHom_isDPMorphism σ J J'⟩

theorem jet_coeffMap : ∀ {R : Type} [CommRing R] (σ : R →+* ℂ) {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (J' : JetRing ℂ I n),
    ∃ τ : J.B →+* J'.B, (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) ∧ IsDPMorphism J.κ J'.κ τ :=
  by
  intro R _ σ I _ n J J'
  exact exists_coeffHom σ J J'

end GlobalTheory.LatJet
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_complex_embedding : ∀ {R : Type} [CommRing R] (σ : R →+* ℂ) {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (J' : JetRing ℂ I n),
    ∃ τ : J.B →+* J'.B, (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) ∧ IsDPMorphism J.κ J'.κ τ := by
  atlas_forward_decl GlobalTheory.LatJet.jet_coeffMap
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

theorem crys_exists_corr : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' B B' : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] {K : Ideal B} {K' : Ideal B'}
    (κ : DividedPowers K) (κ' : DividedPowers K'), IsNilDP κ → IsNilDP κ' →
    ∀ (π : B →+* R) (π' : B' →+* R'), Function.Surjective π → Function.Surjective π' →
    RingHom.ker π = K → RingHom.ker π' = K' → ∀ (τ : B →+* B') (σ : R →+* R')
    {X₀ : Obj F 𝔠 (Sp R)} {Z : Obj F 𝔠 (Sp B)} {i : X₀.A.left ⟶ Z.A.left}, X₀.IsPullBy Z (spMap π) i →
    ∀ {X₁ : Obj F 𝔠 (Sp R')} {Z' : Obj F 𝔠 (Sp B')} {i' : X₁.A.left ⟶ Z'.A.left}, X₁.IsPullBy Z' (spMap π') i' →
    ∀ {q : Z'.A.left ⟶ Z.A.left}, Z'.IsPullBy Z (spMap τ) q → ∀ {p : X₁.A.left ⟶ X₀.A.left}, i' ≫ q = p ≫ i →
    ∀ (M : GrpMor κ (spMap π) X₀.A κ' (spMap π') X₁.A τ (spMap σ) p) (d : Crys κ (spMap π) X₀.A),
    ∃ d', M.Corr d d' := by
  intro H F _ _ 𝔠 R R' B B' _ _ _ _ K K' κ κ' hκ hκ' π π' hπ hπ' hK hK' τ σ X₀ Z i hi X₁ Z' i' hi'
    q hq p hpq M d
  letI := τ.toAlgebra
  have hbc := (H.2.2.1 B Z.A _ Z.ab Z.dim B' Z'.A q hq.grp).1
  obtain ⟨e', he'⟩ := hbc.exists (crysToDR κ hi.grp d)
  obtain ⟨d', hd'⟩ :=
    (GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective H.2.2.2.1 Z'.ab Z'.dim hκ' hπ' hK' hi'.grp).2 e'
  refine ⟨d', fun c ↦ ?_⟩
  obtain ⟨c₁, rfl⟩ := (H.2.2.2.1 B Z.A _ Z.ab Z.dim K κ hκ R π hπ hK X₀.A i hi.grp).2 c
  have k := (liftMor κ hi.grp).comp M
  rw [GrpMor.pull_pull (liftMor κ hi.grp) M k (fun _ ↦ rfl) rfl c₁,
    ← GrpMor.pull_pull (GlobalTheory.Published.AbelianDeRham.bcMor hq.grp) (liftMor κ' hi'.grp) k (fun _ ↦ rfl) hpq c₁,
    ← crysToDR_apply κ' hi'.grp, hd', he']
  rfl

end GlobalTheory.LatJet
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_divided_powers_compatible : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' B B' : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] {K : Ideal B} {K' : Ideal B'}
    (κ : DividedPowers K) (κ' : DividedPowers K'), IsNilDP κ → IsNilDP κ' →
    ∀ (π : B →+* R) (π' : B' →+* R'), Function.Surjective π → Function.Surjective π' →
    RingHom.ker π = K → RingHom.ker π' = K' → ∀ (τ : B →+* B') (σ : R →+* R')
    {X₀ : Obj F 𝔠 (Sp R)} {Z : Obj F 𝔠 (Sp B)} {i : X₀.A.left ⟶ Z.A.left}, X₀.IsPullBy Z (spMap π) i →
    ∀ {X₁ : Obj F 𝔠 (Sp R')} {Z' : Obj F 𝔠 (Sp B')} {i' : X₁.A.left ⟶ Z'.A.left}, X₁.IsPullBy Z' (spMap π') i' →
    ∀ {q : Z'.A.left ⟶ Z.A.left}, Z'.IsPullBy Z (spMap τ) q → ∀ {p : X₁.A.left ⟶ X₀.A.left}, i' ≫ q = p ≫ i →
    ∀ (M : GrpMor κ (spMap π) X₀.A κ' (spMap π') X₁.A τ (spMap σ) p) (d : Crys κ (spMap π) X₀.A),
    ∃ d', M.Corr d d' := by
  atlas_forward_decl GlobalTheory.LatJet.crys_exists_corr
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatJet.BaseChangeFil

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Type} [Fintype I] {n : ℕ}

theorem repr_algebraMap (J : JetRing R I n) (r : R) :
    J.b.repr (algebraMap R J.B r) = Finsupp.single ⟨0, by simp⟩ r := by
  rw [Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_single_one]

theorem map_algebraMap (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) (r : R) :
    τ (algebraMap R J.B r) = algebraMap R' J'.B (σ r) := by
  refine J'.b.ext_elem fun ν ↦ ?_
  rw [hτ, repr_algebraMap, repr_algebraMap, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

theorem map_t (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) (i : I) : τ (J.t i) = J'.t i := by
  refine J'.b.ext_elem fun ν ↦ ?_
  rw [hτ, JetRing.t, JetRing.t, Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

theorem π_surjective (J : JetRing R I n) : Function.Surjective J.π := fun r ↦
  ⟨algebraMap R J.B r, by rw [J.π_eq, repr_algebraMap, Finsupp.single_eq_same]⟩

theorem comp_π (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) : σ.comp J.π = J'.π.comp τ :=
  RingHom.ext fun x ↦ by simp only [RingHom.comp_apply, J.π_eq, J'.π_eq, hτ]

end GlobalTheory.LatJet.BaseChangeFil

open GlobalTheory.LatJet.BaseChangeFil in

theorem GlobalTheory.LatJet.baseChange_liftFil : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left}, X₁.IsPullBy X₀ (spMap σ) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p),
    (∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) → ∀ (τ : J.B →+* J'.B),
    (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) → IsDPMorphism J.κ J'.κ τ →
    ∀ {Z' : Obj F 𝔠 (Sp J'.B)} {q : Z'.A.left ⟶ Y.X'.A.left}, Z'.IsPullBy Y.X' (spMap τ) q →
    ∀ {i' : X₁.A.left ⟶ Z'.A.left} (hi' : X₁.IsPullBy Z' (spMap J'.π) i'), i' ≫ q = p ≫ Y.i →
    ∀ (mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _) (Over.Hom.left (𝟙 X₁.A))),
    ∀ x ∈ Fil X₁.A, ∀ d, IsJetElt J' X₁ N₁ mor' x d → d ∈ liftFil J'.κ hi'.grp := by
  intro hAb F _ _ 𝔠 R R' _ _ σ I _ n J J' X₀ δ₀ N Y X₁ N₁ p hp m hN τ hτ hτdp Z' q hq i' hi' hiq mor'
  have hbc0 := GlobalTheory.T.jet_morphism_is_base_change hAb J X₀ Y.mor
  have hbc1 := GlobalTheory.T.jet_morphism_is_base_change hAb J' X₁ mor'
  have hspan := GlobalTheory.T.lie_filtration_spanned_correspondence hAb σ hp m
  have hb : spMap σ ≫ spMap J.π = spMap J'.π ≫ spMap τ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, comp_π σ J J' τ hτ]
  have M : GrpMor J.κ (spMap J.π) X₀.A J'.κ (spMap J'.π) X₁.A τ (spMap σ) p :=
    GrpMor.of_isGrpPullback hτdp hb hp.grp
  have nq : GrpMor (dp0 J.B) (𝟙 _) Y.X'.A (dp0 J'.B) (𝟙 _) Z'.A τ (spMap τ) q :=
    GrpMor.of_isGrpPullback (Cris.isDPMorphism_of_eq_bot _ rfl _ _) (by simp) hq.grp
  have hspanq := GlobalTheory.T.lie_filtration_spanned_correspondence hAb τ hq nq

  have hprim : ∀ c, c ∈ Submodule.span R' (Set.range m.pull) := by
    letI := σ.toAlgebra
    have hbc := (hAb.2.2.1 R X₀.A _ X₀.ab X₀.dim R' X₁.A p hp.grp).1
    intro c
    obtain ⟨z, rfl⟩ := hbc.2 c
    induction z with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul r c₀ => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c₀, rfl⟩)
  have key : ∀ x₀ ∈ Fil X₀.A, ∀ x, m.Corr x₀ x →
      ∃ d ∈ liftFil J'.κ hi'.grp, IsJetElt J' X₁ N₁ mor' x d := by
    intro x₀ hx₀ x hx
    obtain ⟨e0, he0⟩ := hbc0.exists x₀
    choose e he using fun i ↦ hbc0.exists (N i x₀)
    have hd₀ : IsJetElt J X₀ N Y.mor x₀ (e0 + ∑ i, J.t i • e i) := fun c ↦ by
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, he0 c, fun i ↦ he i c]
    have hd₀F := Y.fil x₀ hx₀ _ hd₀
    obtain ⟨d', hd'⟩ := GlobalTheory.T.nilpotent_divided_powers_compatible hAb J.κ J'.κ J.nil J'.nil J.π J'.π (π_surjective J)
      (π_surjective J') rfl rfl τ σ Y.pull hi' hq hiq M (e0 + ∑ i, J.t i • e i)
    refine ⟨d', hspanq.2.2 _ _ hd₀F (crysToDR_corr J.κ Y.pull.grp hi'.grp M nq hiq hd'), ?_⟩
    intro c
    induction hprim c using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨c₀, rfl⟩ := hc
      have e1 : mor'.pull (m.pull c₀) = M.pull (Y.mor.pull c₀) :=
        (GrpMor.pull_pull m mor' (m.comp mor') (fun _ ↦ rfl) rfl c₀).trans
          (GrpMor.pull_pull Y.mor M (m.comp mor') (fun r ↦ map_algebraMap σ J J' τ hτ r)
            (by simp) c₀).symm
      rw [e1, hd', hd₀ c₀, hx c₀]
      simp only [map_add, map_sum, map_mul, map_algebraMap σ J J' τ hτ, map_t σ J J' τ hτ,
        fun i ↦ hN i x₀ x hx c₀]
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [map_add, ha, hb, Finset.sum_add_distrib, mul_add]
      ring
    | smul r a _ ha =>
      simp only [map_smulₛₗ, LinearMap.map_smul, smul_eq_mul, ha, map_mul, mul_add, Finset.mul_sum,
        RingHom.id_apply]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
  intro x hx d hd
  have hP : ∀ x ∈ Submodule.span R' {x' | ∃ x₀ ∈ Fil X₀.A, m.Corr x₀ x'},
      ∃ d ∈ liftFil J'.κ hi'.grp, IsJetElt J' X₁ N₁ mor' x d := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨x₀, hx₀, hc⟩ := h
      exact key x₀ hx₀ x hc
    | zero => exact ⟨0, zero_mem _, fun c ↦ by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      refine ⟨a + b, add_mem ha hb, fun c ↦ ?_⟩
      simp only [LinearMap.add_apply, ha' c, hb' c, map_add, Finset.sum_add_distrib, mul_add]
      ring
    | smul r x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      refine ⟨algebraMap R' J'.B r • a, Submodule.smul_mem _ _ ha, fun c ↦ ?_⟩
      simp only [LinearMap.smul_apply, ha' c, map_smul, smul_eq_mul, map_mul, mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
  obtain ⟨d', hd'F, hd'⟩ := hP x (hspan.2.1 hx)
  have h0 : mor'.Corr 0 (d - d') := fun c ↦ by
    rw [LinearMap.sub_apply, hd c, hd' c, sub_self, LinearMap.zero_apply, map_zero]
  have h00 : mor'.Corr 0 0 := fun c ↦ by simp
  rw [sub_eq_zero.1 (hbc1.unique h0 h00)]
  exact hd'F
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_family_pullback_first : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left}, X₁.IsPullBy X₀ (spMap σ) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p),
    (∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) → ∀ (τ : J.B →+* J'.B),
    (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) → IsDPMorphism J.κ J'.κ τ →
    ∀ {Z' : Obj F 𝔠 (Sp J'.B)} {q : Z'.A.left ⟶ Y.X'.A.left}, Z'.IsPullBy Y.X' (spMap τ) q →
    ∀ {i' : X₁.A.left ⟶ Z'.A.left} (hi' : X₁.IsPullBy Z' (spMap J'.π) i'), i' ≫ q = p ≫ Y.i →
    ∀ (mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _) (Over.Hom.left (𝟙 X₁.A))),
    ∀ x ∈ Fil X₁.A, ∀ d, IsJetElt J' X₁ N₁ mor' x d → d ∈ liftFil J'.κ hi'.grp := by
  atlas_forward_decl GlobalTheory.LatJet.baseChange_liftFil
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_image_correspondence : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap σ) φ →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) φ) {x : HdR X.A} {x' : HdR X'.A},
    m.Corr x x' → ∀ {v : X.Lie} {v' : X'.Lie}, IsLieImage x v.hom → IsLieImage x' v'.hom →
    Obj.LieCorr σ φ v v' := by
  first | exact @GlobalTheory.RealMult.Obj.lieCorr_of_isLieImage | exact GlobalTheory.RealMult.Obj.lieCorr_of_isLieImage | (intros; apply GlobalTheory.RealMult.Obj.lieCorr_of_isLieImage <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetBCGen

section Coeff

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Type} [Fintype I] {n : ℕ}

theorem repr_algebraMap (J : JetRing R I n) (r : R) (ν : Idx I n) :
    J.b.repr (algebraMap R J.B r) ν = if (⟨0, by simp⟩ : Idx I n) = ν then r else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, J.b.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

open scoped Classical in

theorem repr_t_eq_ite_single (J : JetRing R I n) (i : I) (ν : Idx I n) :
    J.b.repr (J.t i) ν = if (⟨Pi.single i 1, by simp⟩ : Idx I n) = ν then 1 else 0 := by
  rw [JetRing.t, J.b.repr_self, Finsupp.single_apply]

variable (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
  (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν))
include hτ

theorem map_algebraMap (r : R) : τ (algebraMap R J.B r) = algebraMap R' J'.B (σ r) :=
  J'.b.ext_elem fun ν ↦ by rw [hτ, repr_algebraMap, repr_algebraMap]; split_ifs <;> simp

theorem map_t (i : I) : τ (J.t i) = J'.t i :=
  J'.b.ext_elem fun ν ↦ by rw [hτ, repr_t_eq_ite_single, repr_t_eq_ite_single]; split_ifs <;> simp

theorem map_π (x : J.B) : J'.π (τ x) = σ (J.π x) := by rw [J'.π_eq, J.π_eq, hτ]

end Coeff

section Crys

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {S S' : Scheme.{0}} {I : Ideal R}
  {I' : Ideal R'} {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A] {κ' : DividedPowers I'}
  {t' : S' ⟶ Sp R'} {A' : Over S'} [GrpObj A'] {b : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ}

theorem ext_of_isBC (hm : m.IsBC) {d d' : Crys κ' t' A'} (h : ∀ c, d (m.pull c) = d' (m.pull c)) :
    d = d' := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

end Crys

section Jet

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type}
  [Fintype I] {n : ℕ} (J : JetRing R I n) {X : Obj F 𝔠 (Sp R)}
  {m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))}
  (hm : m.IsBC) (N : I → Module.End R (HdR X.A))

def jet (x : HdR X.A) : Crys J.κ (spMap J.π) X.A :=
  hm.bcMap x + ∑ i, J.t i • hm.bcMap (N i x)

theorem isJetElt_jet (x : HdR X.A) : IsJetElt J X N m x (jet J hm N x) := fun c ↦ by
  have e : ∀ y, hm.bcMap y (m.pull c) = algebraMap R J.B (y c) := fun y ↦ (hm.corr_iff.2 rfl) c
  simp only [jet, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, e]

theorem eq_jet_of_isJetElt {x : HdR X.A} {d : Crys J.κ (spMap J.π) X.A} (h : IsJetElt J X N m x d) :
    d = jet J hm N x :=
  ext_of_isBC hm fun c ↦ (h c).trans (isJetElt_jet J hm N x c).symm

theorem jet_add (x y : HdR X.A) : jet J hm N (x + y) = jet J hm N x + jet J hm N y := by
  simp only [jet, map_add, smul_add, Finset.sum_add_distrib]
  abel

theorem jet_smul (r : R) (x : HdR X.A) : jet J hm N (r • x) = algebraMap R J.B r • jet J hm N x := by
  simp only [jet, map_smul, LinearMap.map_smulₛₗ, smul_add, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

end Jet

def compMulti {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {M L : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup L] [Module B L] {K : Type} (δ : L [⋀^K]→ₗ[B] B) (Λ : M → L)
    (hadd : ∀ a b, Λ (a + b) = Λ a + Λ b) (hsmul : ∀ (r : R) a, Λ (r • a) = algebraMap R B r • Λ a) :
    MultilinearMap R (fun _ : K ↦ M) B where
  toFun x := δ (fun j ↦ Λ (x j))
  map_update_add' x j a b := by
    have e : ∀ y, (fun k ↦ Λ (Function.update x j y k)) = Function.update (fun k ↦ Λ (x k)) j (Λ y) :=
      fun y ↦ funext fun k ↦ Function.apply_update (fun _ ↦ Λ) x j y k
    simp only [e, hadd, δ.map_update_add]
  map_update_smul' x j r a := by
    have e : ∀ y, (fun k ↦ Λ (Function.update x j y k)) = Function.update (fun k ↦ Λ (x k)) j (Λ y) :=
      fun y ↦ funext fun k ↦ Function.apply_update (fun _ ↦ Λ) x j y k
    simp only [e, hsmul, δ.map_update_smul, smul_eq_mul, Algebra.smul_def]

end GlobalTheory.JetBCGen

namespace GlobalTheory.JetBCGen

theorem detGen_baseChange : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left}, X₁.IsPullBy X₀ (spMap σ) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p),
    (∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) → ∀ (τ : J.B →+* J'.B),
    (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) → IsDPMorphism J.κ J'.κ τ →
    ∀ {Z' : Obj F 𝔠 (Sp J'.B)} {q : Z'.A.left ⟶ Y.X'.A.left}, Z'.IsPullBy Y.X' (spMap τ) q →
    ∀ {i' : X₁.A.left ⟶ Z'.A.left} (hi' : X₁.IsPullBy Z' (spMap J'.π) i'), i' ≫ q = p ≫ Y.i →
    ∀ (mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _) (Over.Hom.left (𝟙 X₁.A))),
    ∀ (δ₁ : X₁.DetGen), Obj.DetCorr σ p δ₀.1 δ₁.1 → ∀ (δ' : Z'.DetGen), Obj.DetCorr τ q Y.δ'.1 δ'.1 →
    ∀ (x : Fin (Module.finrank ℚ F) → HdR X₁.A) (d : Fin (Module.finrank ℚ F) → Crys J'.κ (spMap J'.π) X₁.A)
      (v : Fin (Module.finrank ℚ F) → X₁.Lie) (v' : Fin (Module.finrank ℚ F) → Z'.Lie),
      (∀ j, IsJetElt J' X₁ N₁ mor' (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧
        IsLieImage (crysToDR J'.κ hi'.grp (d j)) (v' j).hom) →
      δ'.1 v' = algebraMap R' J'.B (δ₁.1 v) := by
  intro H F _ _ 𝔠 R R' _ _ σ I _ n J J' X₀ δ₀ N Y X₁ N₁ p hp m hN τ hτ hτdp Z' q hq i' hi' hcomm mor' δ₁
    hδ₁ δ' hδ' x d v v' hx
  classical
  have hBC' : mor'.IsBC := GlobalTheory.T.jet_morphism_is_base_change H J' X₁ mor'
  have hBC0 : Y.mor.IsBC := GlobalTheory.T.jet_morphism_is_base_change H J X₀ Y.mor
  have L₁ : LieExact X₁.A := (H.2.1 R' X₁.A _ X₁.ab X₁.dim).1
  have L₀ : LieExact X₀.A := (H.2.1 R X₀.A _ X₀.ab X₀.dim).1
  have LY : LieExact Y.X'.A := (H.2.1 J.B Y.X'.A _ Y.X'.ab Y.X'.dim).1
  have LZ : LieExact Z'.A := (H.2.1 J'.B Z'.A _ Z'.ab Z'.dim).1
  have hτa := map_algebraMap σ J J' τ hτ
  have hτt := map_t σ J J' τ hτ
  have hbase : spMap σ ≫ spMap J.π = spMap J'.π ≫ spMap τ := by
    rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    ext y
    exact (map_π σ J J' τ hτ y).symm
  have M : GrpMor J.κ (spMap J.π) X₀.A J'.κ (spMap J'.π) X₁.A τ (spMap σ) p :=
    GrpMor.of_isGrpPullback hτdp hbase hp.grp
  have nq : GrpMor (dp0 J.B) (𝟙 _) Y.X'.A (dp0 J'.B) (𝟙 _) Z'.A τ (spMap τ) q :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) hq.grp
  have K := Y.mor.comp M
  have key : ∀ c₀, M.pull (Y.mor.pull c₀) = mor'.pull (m.pull c₀) := fun c₀ ↦
    (GrpMor.pull_pull Y.mor M K (fun _ ↦ rfl) rfl c₀).trans
      (GrpMor.pull_pull m mor' K (fun r ↦ (hτa r).symm) (by simp) c₀).symm

  have hM : ∀ x₀ y, m.Corr x₀ y → M.Corr (jet J hBC0 N x₀) (jet J' hBC' N₁ y) := by
    intro x₀ y hy c
    obtain ⟨z, rfl⟩ := hBC0.2 c
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b c₀ =>
      rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, key,
        isJetElt_jet J' hBC' N₁ y (m.pull c₀), isJetElt_jet J hBC0 N x₀ c₀]
      have e : ∀ i, N₁ i y (m.pull c₀) = σ (N i x₀ c₀) := fun i ↦ hN i x₀ y hy c₀
      simp only [e, hy c₀, map_add, map_sum, map_mul, hτa, hτt]

  let Λ : HdR X₁.A → Z'.Lie := fun y ↦ LZ.toLie Z'.rm (crysToDR J'.κ hi'.grp (jet J' hBC' N₁ y))
  have hΛadd : ∀ a b, Λ (a + b) = Λ a + Λ b := fun a b ↦ by
    simp only [Λ, jet_add, map_add]
  have hΛsmul : ∀ (r : R') a, Λ (r • a) = algebraMap R' J'.B r • Λ a := fun r a ↦ by
    simp only [Λ, jet_smul, map_smul]
  let Φ₁ := compMulti δ'.1 Λ hΛadd hΛsmul
  let Φ₂ : MultilinearMap R' (fun _ : Fin (Module.finrank ℚ F) ↦ HdR X₁.A) J'.B :=
    (Algebra.linearMap R' J'.B).compMultilinearMap
      (δ₁.1.toMultilinearMap.compLinearMap fun _ ↦ L₁.toLie X₁.rm)
  have hΦ : Φ₁ = Φ₂ := by
    obtain ⟨hspan, -, -⟩ := GlobalTheory.T.lie_filtration_spanned_correspondence H σ hp m
    refine MultilinearMap.ext_of_span_eq_top
      (g := fun (_ : Fin (Module.finrank ℚ F)) (y : {y : HdR X₁.A // ∃ y₀, m.Corr y₀ y}) ↦ y.1)
      (fun _ ↦ ?_) fun s ↦ ?_
    · change Submodule.span R' (Set.range Subtype.val) = ⊤
      rw [Subtype.range_coe_subtype]
      exact hspan
    choose x₀ hx₀ using fun j ↦ (s j).2
    let v₀ := fun j ↦ L₀.toLie X₀.rm (x₀ j)
    let w := fun j ↦ LY.toLie Y.X'.rm (crysToDR J.κ Y.pull.grp (jet J hBC0 N (x₀ j)))
    have hgen := Y.gen x₀ (fun j ↦ jet J hBC0 N (x₀ j)) v₀ w fun j ↦
      ⟨isJetElt_jet J hBC0 N (x₀ j), (L₀.toLie_eq_iff _).1 rfl, (LY.toLie_eq_iff _).1 rfl⟩
    have hl₁ : ∀ j, Obj.LieCorr σ p (v₀ j) (L₁.toLie X₁.rm (s j).1) := fun j ↦
      GlobalTheory.T.lie_image_correspondence H σ hp m (hx₀ j) ((L₀.toLie_eq_iff _).1 rfl) ((L₁.toLie_eq_iff _).1 rfl)
    have hlZ : ∀ j, Obj.LieCorr τ q (w j) (Λ (s j).1) := fun j ↦
      GlobalTheory.T.lie_image_correspondence H τ hq nq (crysToDR_corr J.κ Y.pull.grp hi'.grp M nq hcomm (hM _ _ (hx₀ j)))
        ((LY.toLie_eq_iff _).1 rfl) ((LZ.toLie_eq_iff _).1 rfl)
    change δ'.1 (fun j ↦ Λ (s j).1) = algebraMap R' J'.B (δ₁.1 fun j ↦ L₁.toLie X₁.rm (s j).1)
    rw [hδ' w _ hlZ, hgen, hτa, hδ₁ v₀ _ hl₁]
  have hv' : v' = fun j ↦ Λ (x j) := funext fun j ↦
    ((LZ.toLie_eq_iff Z'.rm).2 (by rw [← eq_jet_of_isJetElt J' hBC' N₁ (hx j).1]; exact (hx j).2.2)).symm
  have hv : v = fun j ↦ L₁.toLie X₁.rm (x j) := funext fun j ↦ ((L₁.toLie_eq_iff X₁.rm).2 (hx j).2.1).symm
  subst hv hv'
  exact DFunLike.congr_fun hΦ x

end GlobalTheory.JetBCGen
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_family_pullback_second : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left}, X₁.IsPullBy X₀ (spMap σ) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p),
    (∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) → ∀ (τ : J.B →+* J'.B),
    (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) → IsDPMorphism J.κ J'.κ τ →
    ∀ {Z' : Obj F 𝔠 (Sp J'.B)} {q : Z'.A.left ⟶ Y.X'.A.left}, Z'.IsPullBy Y.X' (spMap τ) q →
    ∀ {i' : X₁.A.left ⟶ Z'.A.left} (hi' : X₁.IsPullBy Z' (spMap J'.π) i'), i' ≫ q = p ≫ Y.i →
    ∀ (mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _) (Over.Hom.left (𝟙 X₁.A))),
    ∀ (δ₁ : X₁.DetGen), Obj.DetCorr σ p δ₀.1 δ₁.1 → ∀ (δ' : Z'.DetGen), Obj.DetCorr τ q Y.δ'.1 δ'.1 →
    ∀ (x : Fin (Module.finrank ℚ F) → HdR X₁.A) (d : Fin (Module.finrank ℚ F) → Crys J'.κ (spMap J'.π) X₁.A)
      (v : Fin (Module.finrank ℚ F) → X₁.Lie) (v' : Fin (Module.finrank ℚ F) → Z'.Lie),
      (∀ j, IsJetElt J' X₁ N₁ mor' (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧
        IsLieImage (crysToDR J'.κ hi'.grp (d j)) (v' j).hom) →
      δ'.1 v' = algebraMap R' J'.B (δ₁.1 v) := by
  atlas_forward_decl GlobalTheory.JetBCGen.detGen_baseChange
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatJet

theorem jet_pi_tau {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) : J'.π.comp τ = σ.comp J.π := by
  ext x; simp only [RingHom.comp_apply, J.π_eq, J'.π_eq, hτ]

theorem jet_pi_alg {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) :
    J.π.comp (algebraMap R J.B) = RingHom.id R := by
  ext r
  simp only [RingHom.comp_apply, RingHom.id_apply, J.π_eq, Algebra.algebraMap_eq_smul_one, map_smul, ← J.one]
  simp

theorem family_bc (H : GlobalTheory.Published.AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')} {δ₁ : X₁.DetGen}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left} (hp : X₁.IsPullBy X₀ (spMap σ) p)
    (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p) (hδ : Obj.DetCorr σ p δ₀.1 δ₁.1)
    (hN : ∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) (hτdp : IsDPMorphism J.κ J'.κ τ) :
    ∃ (Y' : Family J' X₁ δ₁ N₁) (q : Y'.X'.A.left ⟶ Y.X'.A.left),
      Y'.X'.IsPullBy Y.X' (spMap τ) q ∧ Obj.DetCorr τ q Y.δ'.1 Y'.δ'.1 := by
  obtain ⟨Z', q, hq⟩ := Obj.exists_isPullBy Y.X' (spMap τ)
  have e1 : spMap σ ≫ spMap J.π = spMap J'.π ≫ spMap τ := by
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, jet_pi_tau σ J J' τ hτ]
  have h1 := hp.comp Y.pull
  rw [e1] at h1
  obtain ⟨i', hi', hi'q⟩ := h1.cancel hq
  obtain ⟨δ', hδ', -⟩ := hq.existsUnique_detGen τ Y.δ'
  have hb : 𝟙 (Sp R') = spMap J'.π ≫ spMap (algebraMap R' J'.B) := by
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, jet_pi_alg]; exact (Spec.map_id _).symm
  have mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _)
      (Over.Hom.left (𝟙 X₁.A)) := GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _) hb (𝟙 X₁.A)
  exact ⟨{ X' := Z', i := i', pull := hi', mor := mor', δ' := δ'
           fil := GlobalTheory.T.jet_family_pullback_first H σ J J' Y hp m hN τ hτ hτdp hq hi' hi'q mor'
           gen := GlobalTheory.T.jet_family_pullback_second H σ J J' Y hp m hN τ hτ hτdp hq hi' hi'q mor' δ₁ hδ δ' hδ' }, q, hq, hδ'⟩

theorem jetBC_of_grothendieckDeformation_abelianDeRham : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → JetBC := by
  intro _ H E _ _ _ I _ 𝔠 φ L R _ _ _ σ n J J' X₀ δ₀ N Y T hT
  obtain ⟨p, m, hp, hδ, hN⟩ := hT
  obtain ⟨τ, hτ, hτdp⟩ := GlobalTheory.T.jet_ring_complex_embedding σ J J'
  obtain ⟨Y', q, hq, hδ'⟩ := family_bc H σ J J' Y hp m hδ hN τ hτ hτdp
  exact ⟨Y', τ, q, hτ, hq, hδ'⟩

end GlobalTheory.LatJet
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_base_change_of_deformation : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → JetBC := by
  atlas_forward_decl GlobalTheory.LatJet.jetBC_of_grothendieckDeformation_abelianDeRham
end
