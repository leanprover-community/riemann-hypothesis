import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellPointEqOfTriangularFrames

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
namespace GlobalTheory

theorem preimage_opens_eq_range_of_valuative (F Z X : Scheme.{0}) (j : F ⟶ Z) (π : Z ⟶ X) (U : X.Opens)
    (hj : IsOpenImmersion j) (hd : Dense (Set.range j)) (hπ : IsSeparated π)
    (hF : TopologicalSpace.NoetherianSpace F) (hU : Set.range (j ≫ π) ⊆ (U : Set X))
    (hv : ∀ (A K : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K]
      [IsFractionRing A K] (a : Sp K ⟶ F) (b : Sp A ⟶ X), Set.range b ⊆ (U : Set X) →
      a ≫ j ≫ π = spMap (algebraMap A K) ≫ b →
      ∃ l : Sp A ⟶ F, spMap (algebraMap A K) ≫ l = a ∧ l ≫ j ≫ π = b) :
    π ⁻¹' (U : Set X) = Set.range j := by
  have hg : Set.range (j ≫ π).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hU
  let g : F ⟶ U := IsOpenImmersion.lift U.ι (j ≫ π) hg
  have hgfac : g ≫ U.ι = j ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hj' : Set.range j.base ⊆ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨x, rfl⟩
  let j' : F ⟶ (π ⁻¹ᵁ U : Z.Opens) := IsOpenImmersion.lift (π ⁻¹ᵁ U).ι j hj'
  have hj'fac : j' ≫ (π ⁻¹ᵁ U).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hcomp : j' ≫ (π ∣_ U) = g := by
    rw [← cancel_mono U.ι, hgfac, Category.assoc, morphismRestrict_ι, ← Category.assoc, hj'fac]
  haveI : QuasiCompact g := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  haveI : UniversallyClosed g := by
    apply UniversallyClosed.of_valuativeCriterion
    intro S
    obtain ⟨l, hl1, hl2⟩ := hv S.R S.K S.i₁ (S.i₂ ≫ U.ι)
      (by
        rintro _ ⟨x, rfl⟩
        rw [← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩)
      (by rw [← hgfac, ← Category.assoc, S.commSq.w, Category.assoc])
    have hl3 : l ≫ g = S.i₂ := by
      rw [← cancel_mono U.ι, Category.assoc, hgfac, hl2]
    exact ⟨⟨{ l := l, fac_left := hl1, fac_right := hl3 }⟩⟩
  haveI : UniversallyClosed (j' ≫ (π ∣_ U)) := by rw [hcomp]; infer_instance
  haveI : IsSeparated ((π ⁻¹ᵁ U).ι ≫ π) := inferInstance
  haveI : IsSeparated ((π ∣_ U) ≫ U.ι) := by rw [morphismRestrict_ι]; infer_instance
  haveI : IsSeparated (π ∣_ U) := IsSeparated.of_comp (π ∣_ U) U.ι
  haveI : UniversallyClosed j' := UniversallyClosed.of_comp_of_isSeparated j' (π ∣_ U)
  have hclosed : IsClosed (Set.range j'.base) := j'.isClosedMap.isClosed_range
  have hrange : Set.range j' = (π ⁻¹ᵁ U).ι ⁻¹' Set.range j := by
    ext w; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, (π ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hj'fac, hx]
  have hdense : Dense (Set.range j') := by
    rw [hrange]; exact hd.preimage (π ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap
  have huniv : Set.range j' = Set.univ := by
    rw [← hclosed.closure_eq]; exact hdense.closure_eq
  ext z; constructor
  · intro hz
    have hz' : z ∈ Set.range (π ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hz
    obtain ⟨w, rfl⟩ := hz'
    obtain ⟨x, rfl⟩ : w ∈ Set.range j' := huniv ▸ Set.mem_univ w
    exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, rfl⟩; exact hU ⟨x, rfl⟩

end GlobalTheory
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Valu

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_surj {k B : Type} [CommRing k] [CommRing B] (x : Sp k ⟶ Sp B) : ∃ β : B →+* k, x = spMap β :=
  ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩

theorem exists_of_closedPoint {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.affineOpens) (hx : x (IsLocalRing.closedPoint A) ∈ (U.1 : Set X)) :
    ∃ φ : Γ(X, U.1) →+* A, x = spMap φ ≫ U.2.fromSpec := by
  have htop : x ⁻¹ᵁ U.1 = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem x hx
  have hr : Set.range x ⊆ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : y ∈ x ⁻¹ᵁ U.1 := by rw [htop]; trivial
    exact this
  have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  obtain ⟨φ, hφ⟩ := sp_surj (B := Γ(X, U.1)) (@IsOpenImmersion.lift _ _ _ U.2.fromSpec x hi hr)
  exact ⟨φ, (@IsOpenImmersion.lift_fac _ _ _ U.2.fromSpec x hi hr).symm.trans (congrArg (· ≫ U.2.fromSpec) hφ)⟩

theorem indep_cellVec {T : Type} {m : T → ℕ} {k : Type} [Field k] {M : ℕ} (D c : Let m → Fin (M + 1) → k) (w : Pm m)
    (x : CellVar m → k) (h : LeftInv D c) (τ : T) :
    LinearIndependent k fun j : Fin (m τ) => cellVec c w x ⟨τ, j⟩ := by
  have h1 := (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m k M D c w x h).1 _ _ (down_std τ (m τ) le_rfl)
  rw [GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.1] at h1
  have h2 := Matrix.linearIndependent_rows_of_det_ne_zero (h1.trans_ne one_ne_zero)
  let L : (Fin (M + 1) → k) →ₗ[k] (Fin (m τ) → k) :=
    Matrix.toLin' (Matrix.of fun l' r => D ((wLet w ∘ std τ (m τ) le_rfl) l') r)
  exact LinearIndependent.of_comp L h2

theorem inBlock_cellVec {T : Type} {m : T → ℕ} {S ι : Type} [CommRing S] {c c' : Let m → ι → S} (h : InBlock c c')
    (w : Pm m) (x : CellVar m → S) : InBlock c (cellVec c' w x) := fun z =>
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h ⟨z.1, w z.1 i⟩)

theorem map_uvec {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens} {S : Type} [CommRing S]
    (c : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) (ψ : CR m U →+* S) :
    (fun z => ψ ∘ uvec c w z) =
      cellVec (fun z => (ψ.comp (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) ∘ c z) w (ψ ∘ MvPolynomial.X) :=
  funext fun z => map_cellVec ψ _ w _ z

theorem sp_cbase {X : Scheme.{0}} {T : Type} {m : T → ℕ} {U : X.affineOpens} {S : Type} [CommRing S]
    (ψ : CR m U →+* S) :
    spMap ψ ≫ cbase m U = spMap (ψ.comp (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) ≫ U.2.fromSpec := by
  rw [cbase, ← Category.assoc, sp_comp]

theorem exists_integral_cell : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (A k : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [Algebra A k] [IsFractionRing A k] b' w' (a : Sp k ⟶ Sp (CR m (V b'))) (x : Sp A ⟶ X), Set.range x ⊆ ⋃ b, ((V b).1 : Set X) → a ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x → ∃ b w, ∃ l : Sp A ⟶ Sp (CR m (V b)), l ≫ cbase m (V b) = x ∧ spMap (algebraMap A k) ≫ l ≫ h b w = a ≫ h b' w' := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hC hP A k _ _ _ _ _ _ b' w' a x hx ha
  obtain ⟨ψ', rfl⟩ := sp_surj a
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hx ⟨IsLocalRing.closedPoint A, rfl⟩)
  obtain ⟨φ, rfl⟩ := exists_of_closedPoint x (V b) hb
  have ha' : spMap ((algebraMap A k).comp φ) ≫ (V b).2.fromSpec =
      spMap (ψ'.comp (MvPolynomial.C : Γ(X, (V b').1) →+* CR m (V b'))) ≫ (V b').2.fromSpec := by
    rw [← sp_cbase, ha, ← Category.assoc, sp_comp]
  obtain ⟨w, y, d, hy, hd, ht⟩ := GlobalTheory.T.exists_integral_flagCell_of_valuedField T m k (ValuationRing.valuation A k).valuationSubring M _ _
    (inBlock_cellVec (hC.compat k b b' _ _ ha') w' (ψ' ∘ MvPolynomial.X))
    (indep_cellVec _ _ w' _ ((hC.inv b').map _))
  have hy' : ∀ v, ∃ t : A, algebraMap A k t = y v := fun v => (ValuationRing.mem_integer_iff A k (y v)).1 (hy v)
  choose t hyt using hy'
  let χ : CR m (V b) →+* A := MvPolynomial.eval₂Hom φ t
  have hχ : χ.comp (MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)) = φ := MvPolynomial.eval₂Hom_comp_C φ t
  have hχ' : ((algebraMap A k).comp χ).comp (MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)) =
      (algebraMap A k).comp φ := by rw [RingHom.comp_assoc, hχ]
  refine ⟨b, w, spMap χ, by rw [sp_cbase, hχ], ?_⟩
  rw [← Category.assoc, sp_comp]
  refine GlobalTheory.T.flagCell_point_eq_of_triangular_frames O K β X s T m M B V α c D P p0 p h hC hP k b b' w w' _ ψ' d ?_ hd ?_
  · rw [sp_cbase, sp_cbase, hχ', ha']
  · have e : ((algebraMap A k).comp χ) ∘ MvPolynomial.X = y := funext fun v => by
      rw [← hyt]
      exact congrArg (algebraMap A k) (MvPolynomial.eval₂Hom_X' φ t v)
    rw [map_uvec, map_uvec, hχ', e]
    exact ht

end GlobalTheory.FlagEmb.Valu
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCell_valuativeExistence_over_union_of_opens : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (A k : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [Algebra A k] [IsFractionRing A k] b' w' (a : Sp k ⟶ Sp (CR m (V b'))) (x : Sp A ⟶ X), Set.range x ⊆ ⋃ b, ((V b).1 : Set X) → a ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x → ∃ b w, ∃ l : Sp A ⟶ Sp (CR m (V b)), l ≫ cbase m (V b) = x ∧ spMap (algebraMap A k) ≫ l ≫ h b w = a ≫ h b' w' := by
  atlas_forward_decl GlobalTheory.FlagEmb.Valu.exists_integral_cell
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem preimage_iUnion_eq_range_cells : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (F Z : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)) (j : F ⟶ Z) (ν : Z ⟶ P), IsImmersion f → (∀ b w, IsOpenImmersion (i b w)) → (∀ b w, i b w ≫ f = h b w) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → IsOpenImmersion j → j ≫ ν = f → Dense (Set.range j) → TopologicalSpace.NoetherianSpace F → IsSeparated (ν ≫ p0) → (ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X) = Set.range j := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hC hP F Z f i j ν hf hi hif hcov hj hjν hd hF hsep
  have hcb : ∀ b w, i b w ≫ f ≫ p0 = cbase m (V b) := fun b w => by
    rw [← Category.assoc, hif, hP.base]
  have hjf : j ≫ ν ≫ p0 = f ≫ p0 := by rw [← Category.assoc, hjν]
  have hU : ((⨆ b, (V b).1 : X.Opens) : Set X) = ⋃ b, ((V b).1 : Set X) := by
    simp [TopologicalSpace.Opens.coe_iSup]
  rw [← hU]
  refine GlobalTheory.preimage_opens_eq_range_of_valuative F Z X j (ν ≫ p0) _ hj hd hsep hF ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hcov x
    rw [hU, hjf, ← Scheme.Hom.comp_apply, hcb b w]
    refine Set.mem_iUnion.2 ⟨b, ?_⟩
    have hr := (V b).2.range_fromSpec
    unfold cbase
    rw [Scheme.Hom.comp_apply]
    exact hr ▸ Set.mem_range_self _
  · intro A k _ _ _ _ _ _ a x hx hax
    rw [hU] at hx
    haveI : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    haveI : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨y⟩ := ‹Nonempty (Sp k)›
    obtain ⟨b', w', hy⟩ := hcov (a y)
    have hra : Set.range a ⊆ Set.range (i b' w') := by
      rintro _ ⟨z, rfl⟩
      rwa [Subsingleton.elim z y]
    haveI := hi b' w'
    let a' := IsOpenImmersion.lift (i b' w') a hra
    have ha' : a' ≫ i b' w' = a := IsOpenImmersion.lift_fac _ _ _
    have h1 : a' ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x := by
      rw [← hcb b' w', ← Category.assoc, ha', ← hax, hjf]
    obtain ⟨b, w, l, hl, hl2⟩ := GlobalTheory.T.flagCell_valuativeExistence_over_union_of_opens O K β X s T m M B V α c D P p0 p h hC hP A k b' w' a' x hx h1
    haveI : Mono f := inferInstance
    refine ⟨l ≫ i b w, ?_, ?_⟩
    · rw [← cancel_mono f, Category.assoc, Category.assoc, hif, hl2, ← hif b' w', ← Category.assoc, ha']
    · rw [hjf, Category.assoc, hcb b w, hl]

end GlobalTheory.FlagEmb
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_iUnion_opens_eq_range_flagCells : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (F Z : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)) (j : F ⟶ Z) (ν : Z ⟶ P), IsImmersion f → (∀ b w, IsOpenImmersion (i b w)) → (∀ b w, i b w ≫ f = h b w) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → IsOpenImmersion j → j ≫ ν = f → Dense (Set.range j) → TopologicalSpace.NoetherianSpace F → IsSeparated (ν ≫ p0) → (ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X) = Set.range j := by
  atlas_forward_decl GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells
end
