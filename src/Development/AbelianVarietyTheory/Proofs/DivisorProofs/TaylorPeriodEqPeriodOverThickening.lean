import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfComap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEqZeroOfSuccLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticChartsRealizationOfAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassLinearRelationUniqueOfNilpotent
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyShiftMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphic

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer

variable {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ}
  (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R)
  (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k))
  (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C)
  (h1 : ∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f))
  (h3 : ∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1))))
    ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)))

def famObj (S : K₀.DObj et M) : K.Obj where
  k := ka S.T.k
  C := S.T.C
  alg := ((algebraMap R S.T.C).comp θ).toAlgebra
  J := S.T.J
  nil := S.T.nil
  ρ := ρ' S
  ρ_cst := h1 S

def famCoef : CoefMap θ K.Oc (K₀.OD et M) where
  G :=
    { obj := famObj K K₀ et M θ ka ρ' h1
      map {S S'} f :=
        { φ := { (f.1.φ : S.T.C →+* S'.T.C) with commutes' := fun x ↦ f.2 (θ x) }
          deg := f.1.deg
          le := hka (Charts.Hom.le f.1)
          mem := f.1.mem
          close := h3 S S' f }
      map_id _ := Charts.hom_ext (fun _ ↦ rfl) rfl
      map_comp _ _ := Charts.hom_ext (fun _ ↦ rfl) rfl }
  α S := RingHom.id S.T.C
  naturality _ _ := rfl
  smul S d c := (Algebra.smul_def (A := S.T.C) (θ d) c).symm

theorem famCoef_perCl (per : Λ →+ Hol F.V) :
    (famCoef K K₀ et M θ ka hka ρ' h1 h3).pull1 (K.perCl per) = K₀.perClD et M (θ.toAddMonoidHom.comp per) :=
  congrArg (H1.mk _) (Subtype.ext (funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ rfl))

theorem coefD_pull1_of_family (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k))
    (h2 : ∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J)
    {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀}
    {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : Real K s σ) (r₀ : Real K₀ s₀ σ₀) {J : Ideal D}
    (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io)
    (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀) (h4 : ∀ b, θ (σ b) = io (j b))
    (h5 : ∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) (c : FirstDeRham s) (per : Λ →+ Hol F.V)
    (hc : r.coef.pull1 c = K.perCl per) (h1 : ∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f))
    (h3 : ∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1))))
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) :
    (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) := by
  let t : (r.coef.comp (famCoef K K₀ et M θ ka hka ρ' h1 h3)).G ⟶ (n.coef.comp (r₀.coefD dl H)).G :=
    { app S :=
        { φ := { RingHom.id S.T.C with commutes' := fun b ↦ congrArg (algebraMap R S.T.C) (h4 b) }
          φ₀ := RingHom.id (S.T.C ⧸ S.T.J)
          comm := fun _ ↦ rfl
          dp := letI := S.T.ratAlg; isDPMorphism_of_rat (C := S.T.C) (C' := S.T.C) _ _ (RingHom.id S.T.C) fun _ h ↦ h
          pt := by
            have e : (Ideal.Quotient.mk S.T.J).comp (ρ' S) = ((Ideal.Quotient.mk S.T.J).comp S.T.ρ).comp (res _) :=
              RingHom.ext fun h ↦ Ideal.Quotient.eq.2 (h2 S h)
            change spMap (RingHom.id (S.T.C ⧸ S.T.J)) ≫ spMap ((Ideal.Quotient.mk S.T.J).comp (ρ' S)) ≫ r.x (ka S.T.k) =
              (spMap ((Ideal.Quotient.mk S.T.J).comp S.T.ρ) ≫ r₀.x S.T.k) ≫ φ₀
            rw [Cris.spMap_id, Category.id_comp, Category.assoc, ← h5, e, Cris.spMap_comp (res _), Category.assoc] }
      naturality _ _ _ := Thick.hom_ext fun _ ↦ rfl }
  refine (n.coef.pullCohomologyOne_comp (r₀.coefD dl H) c).symm.trans ?_
  refine (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ t (fun _ _ ↦ rfl) c).symm.trans ?_
  rw [CoefMap.pullCohomologyOne_comp, hc, famCoef_perCl]

end GlobalTheory.AnPer

open GlobalTheory.AnPer in

theorem GlobalTheory.AnPer.period_restrict_family : ∀ {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)) (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C), (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) → (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) → (∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) → ∀ {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀} {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : GlobalTheory.AnPer.Real K s σ) (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀), (∀ b, θ (σ b) = io (j b)) → (∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), r.coef.pull1 c = K.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) :=
  fun K K₀ _ _ et M θ ka hka res ρ' h1 h2 h3 _ _ _ _ _ _ _ _ _ _ _ _ r r₀ _ dl _ _ _ H j φ₀ n h4 h5 c per hc ↦
    coefD_pull1_of_family K K₀ et M θ ka hka ρ' res h2 r r₀ dl H j φ₀ n h4 h5 c per hc h1 h3
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_over_ring_restrict_family_class : ∀ {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)) (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C), (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) → (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) → (∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) → ∀ {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀} {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : GlobalTheory.AnPer.Real K s σ) (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀), (∀ b, θ (σ b) = io (j b)) → (∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), r.coef.pull1 c = K.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) := by
  atlas_forward_decl GlobalTheory.AnPer.period_restrict_family
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem period_const_ext : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) {B₀ D : Type} [CommRing B₀] [CommRing D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp B₀} {σ₀ : B₀ →+* Hol F₀.V} (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B₀ →+* D) (φ₀ : X₀ ⟶ X₀) (n : IsMor (dp0 B₀) s₀ dl s' j φ₀), φ₀ = 𝟙 X₀ → (∀ b, et (σ₀ b) = io (j b)) → ∀ (c : FirstDeRham s₀) (per : Λ →+ Hol F₀.V), r₀.coef.pull1 c = K₀.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (et.toAddMonoidHom.comp per) := by
  intro I₀ _ g Λ _ F₀ K₀ R _ et M B₀ D _ _ X₀ s₀ σ₀ r₀ J dl s' π io H j φ₀ n hφ hj c per hc
  refine GlobalTheory.T.period_over_ring_restrict_family_class K₀ K₀ et M et id (fun h ↦ h) (fun _ ↦ RingHom.id _) (fun S ↦ S.T.ρ)
    (fun S f ↦ (S.T.ρ_cst f).trans (S.compat f)) (fun S h ↦ ?_) (fun S S' f ↦ Charts.Hom.close f.1)
    r₀ r₀ dl H j φ₀ n hj (fun k ↦ ?_) c per hc
  · exact (sub_self (S.T.ρ h)).symm ▸ S.T.J.zero_mem
  · subst hφ
    have e : spMap (RingHom.id (Hol (K₀.W k))) = 𝟙 _ := Spec.map_id _
    exact (congrArg (· ≫ r₀.x k) e).trans ((Category.id_comp _).trans (Category.comp_id _).symm)

end GlobalTheory.AnPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefD_pull1_eq_perClD_of_pull1_eq_perCl : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) {B₀ D : Type} [CommRing B₀] [CommRing D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp B₀} {σ₀ : B₀ →+* Hol F₀.V} (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B₀ →+* D) (φ₀ : X₀ ⟶ X₀) (n : IsMor (dp0 B₀) s₀ dl s' j φ₀), φ₀ = 𝟙 X₀ → (∀ b, et (σ₀ b) = io (j b)) → ∀ (c : FirstDeRham s₀) (per : Λ →+ Hol F₀.V), r₀.coef.pull1 c = K₀.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (et.toAddMonoidHom.comp per) := by
  atlas_forward_decl GlobalTheory.AnPer.period_const_ext
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem taylor_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → ∀ τ : (I → ℂ) → Fin g → ℂ, AnalyticAt ℂ τ 0 → ∃ n : Fin r → Fin g → R, (∀ j a, n j a ∈ J) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, taylor N (fun i ↦ ∑ j, m j i) (fun z ↦ τ z a) - algebraMap ℂ R (τ 0 a) = ∑ j, n j a := by
  intro I _ _ g R _ _ J N hJ r
  induction r with
  | zero =>
    intro m _ _ τ _
    refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun a => ?_⟩
    have h := (taylor_formal_properties N (fun i ↦ ∑ j : Fin 0, m j i)).2.2.2.2.2 (fun z ↦ τ z a)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
    have : Set.range (fun _ : I => (0 : R)) ⊆ {0} := by
      rintro _ ⟨_, rfl⟩; rfl
    have hb : Ideal.span (Set.range (fun _ : I => (0 : R))) = ⊥ := by
      rw [Ideal.span_eq_bot]; rintro _ ⟨_, rfl⟩; rfl
    rw [hb, Ideal.mem_bot] at h
    exact h
  | succ r ih =>
    intro m hmJ hm τ hτ
    obtain ⟨n', hn'J, hn', hn'eq⟩ := ih (fun j => m (Fin.castSucc j)) (fun j i => hmJ _ i)
      (fun j i i' => hm _ i i') τ hτ
    set t : I → R := fun i => ∑ j : Fin r, m (Fin.castSucc j) i with ht
    set l : I → R := fun i => m (Fin.last r) i with hl
    let v : Fin g → R := fun a => ∑ i, taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i 1)) * l i
    have htJ : ∀ i, t i ∈ J := fun i => J.sum_mem fun j _ => hmJ _ i
    have hlJ : ∀ i, l i ∈ J := fun i => hmJ _ i
    have hspan : Ideal.span (Set.range t ∪ Set.range l) ≤ J := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact htJ i
      · exact hlJ i
    have hvJ : ∀ a, v a ∈ J := fun a => J.sum_mem fun i _ => J.mul_mem_left _ (hlJ i)
    have hv : ∀ a b, v a * v b = 0 := by
      intro a b
      simp only [v, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
      have := hm (Fin.last r) i' i
      calc _ = (taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z b) z (Pi.single i 1)) *
              taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i' 1))) * (l i' * l i) := by ring
        _ = 0 := by simp only [hl, this, mul_zero]
    refine ⟨Fin.snoc (α := fun _ => Fin g → R) n' v, ?_, ?_, ?_⟩
    · intro j a
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hvJ a
      · simpa using hn'J j a
    · intro j a b
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hv a b
      · simpa using hn' j a b
    · intro a
      have hfa : AnalyticAt ℂ (fun z ↦ τ z a) 0 :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) a).analyticAt (τ 0)).comp hτ
      have hsum : (fun i ↦ ∑ j : Fin (r + 1), m j i) = fun i => t i + l i := by
        funext i; simp only [ht, hl, Fin.sum_univ_castSucc]
      have hstep := taylor_add_of_mul_eq_zero N t l
        (fun s hs => hJ s fun a => hspan (hs a)) (fun i j => hm (Fin.last r) i j) _ hfa
      rw [hsum, hstep, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [← hn'eq a]
      simp only [v, t]
      ring

end GlobalTheory.PeriodFamily
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_sub_value_eq_sum_sqZero_vector : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → ∀ τ : (I → ℂ) → Fin g → ℂ, AnalyticAt ℂ τ 0 → ∃ n : Fin r → Fin g → R, (∀ j a, n j a ∈ J) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, taylor N (fun i ↦ ∑ j, m j i) (fun z ↦ τ z a) - algebraMap ℂ R (τ 0 a) = ∑ j, n j a := by
  atlas_forward_decl GlobalTheory.PeriodFamily.taylor_sub_value_eq_sum_sqZero
end

section
section
open Filter Topology TopologicalSpace TensorProduct
open GlobalTheory.AnPer GlobalTheory.PeriodFamily

namespace GlobalTheory.AnPer

theorem evT_map_shA {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
    {R : Type} [CommRing R] [Algebra ℂ R] {l : Λ} {k k' : K.K} (h : K.le l k' k) (p : Tot I g) (hp : p ∈ K.W k')
    (y : R ⊗[ℂ] Hol (K.W k)) :
    evT R p hp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h) y) =
      evT R (F.shift l p) (K.maps h p hp) y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply, AlgHom.comp_apply, Hol.ev_apply, Hol.ev_apply, Charts.shA_apply, Charts.fn_sh h y hp]
    rfl

theorem close_taylor_shift : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (ρ : Hol (K.W k) →+* R ⊗[ℂ] Hol (K₀.W k₀)) (ρ' : Hol (K.W k') →+* R ⊗[ℂ] Hol (K₀.W k₀')), IsTay N (fun i ↦ ∑ j, m j i) ρ → IsTay N (fun i ↦ ∑ j, m j i) ρ' → Close (J.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k₀'))) (ρ'.comp (Charts.sh h)) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ) := by
  intro I _ _ g Λ _ F F₀ K K₀ R _ _ J N hJ r m hm hmm hτ l k k' k₀ k₀' h h₀ hW ρ ρ' hρ hρ'
  by_cases hne : ∃ p, p ∈ K₀.W k₀'
  swap
  · have e : ρ'.comp (Charts.sh h) =
        (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ :=
      RingHom.ext fun f ↦ GlobalTheory.tensor_hol_ext_of_values _ _ _ _ fun p hp ↦ (hne ⟨p, hp⟩).elim
    rw [e]
    exact Relation.ReflTransGen.refl
  obtain ⟨p₀, hp₀⟩ := hne
  have h0 : (0 : I → ℂ) ∈ F.V := K.base k' _ (hW p₀ hp₀)
  have hτa : AnalyticAt ℂ (F.τ l) 0 := F.hol l _ h0
  obtain ⟨n, hn, hnn, hd⟩ := GlobalTheory.T.taylor_sub_value_eq_sum_sqZero_vector J N hJ r m hm hmm (F.τ l) hτa
  have ht : ∀ i, (fun i ↦ ∑ j, m j i) i ∈ J := fun i ↦ J.sum_mem fun j _ ↦ hm j i
  have htN : ∀ s : Fin (N + 1) → I, ∏ a, (fun i ↦ ∑ j, m j i) (s a) = 0 :=
    fun s ↦ hJ _ fun a ↦ ht (s a)
  have hin : ∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2 + F.τ l 0) : Tot I g) ∈ K.W k :=
    fun p hp ↦ K.maps h _ (hW p hp)
  obtain ⟨-, -, hconst, hgerm, -, -⟩ := taylor_formal_properties N (fun i ↦ ∑ j, m j i)
  refine close_of_sliceTaylor J N hJ _ ht r n hn hnn (K.W k) (K₀.W k₀') (fun p ↦ p.2 + F.τ l 0)
    (fun p _ ↦ analyticAt_snd.add analyticAt_const) hin _ _ ?_ ?_
  · intro f p hp
    refine (hρ' (Charts.sh h f) p hp).trans ?_
    have hc : ContinuousAt (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) 0 := by fun_prop
    have e : (fun z ↦ (Charts.sh h f).fn (z, p.2)) =ᶠ[𝓝 0] fun z ↦ f.fn (z, p.2 + F.τ l z) := by
      filter_upwards [hc.preimage_mem_nhds ((K.W k').isOpen.mem_nhds (hW p hp))] with z hz
      exact Charts.fn_sh h f hz
    rw [hgerm _ _ e, taylor_shear N _ htN f.fn (F.τ l) p.2 hτa (f.analytic _ (hin p hp))]
    simp only [hd]
  · intro f p hp
    refine (evT_map_shA h₀ p hp (ρ f)).trans ?_
    refine (hρ f _ _).trans ?_
    have e : (F₀.shift l p).2 = p.2 + F.τ l 0 := by
      change p.2 + F₀.τ l p.1 = _
      rw [hτ]
    rw [e]
    refine (taylor_shear N _ htN f.fn (fun _ ↦ F.τ l 0) p.2 analyticAt_const (f.analytic _ (hin p hp))).trans ?_
    simp only [hconst, sub_self]

end GlobalTheory.AnPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.close_taylor_shift_alt : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (ρ : Hol (K.W k) →+* R ⊗[ℂ] Hol (K₀.W k₀)) (ρ' : Hol (K.W k') →+* R ⊗[ℂ] Hol (K₀.W k₀')), IsTay N (fun i ↦ ∑ j, m j i) ρ → IsTay N (fun i ↦ ∑ j, m j i) ρ' → Close (J.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k₀'))) (ρ'.comp (Charts.sh h)) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ) := by
  atlas_forward_decl GlobalTheory.AnPer.close_taylor_shift
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isTay_apply_of_fn_eq_param : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (f : (I → ℂ) → ℂ), (∀ p ∈ W, h.fn p = f p.1) → ρ h = GlobalTheory.PeriodFamily.taylor N t f ⊗ₜ[ℂ] 1 := by
  intro I _ _ g R _ _ N t W W₀ h0 ρ hρ h f hf
  apply GlobalTheory.tensor_hol_ext_of_values W₀ R
  intro p hp
  have e1 := hρ h p hp
  have e2 : (fun z : I → ℂ ↦ h.fn (z, p.2)) =ᶠ[𝓝 0] f := by
    have hc : Continuous (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) := continuous_id.prodMk continuous_const
    have hm : ∀ᶠ z in 𝓝 (0 : I → ℂ), ((z, p.2) : Tot I g) ∈ W :=
      hc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds (h0 p hp))
    filter_upwards [hm] with z hz using hf _ hz
  have e3 := (GlobalTheory.PeriodFamily.taylor_formal_properties (D := R) N t).2.2.2.1 _ _ e2
  change evT R p hp (ρ h) = evT R p hp (GlobalTheory.PeriodFamily.taylor N t f ⊗ₜ[ℂ] (1 : Hol W₀))
  rw [e1, e3]
  simp [evT, Algebra.TensorProduct.lift_tmul]

end GlobalTheory.AnPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParameterTaylorExpansionHom_apply_of_param_only : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (f : (I → ℂ) → ℂ), (∀ p ∈ W, h.fn p = f p.1) → ρ h = taylor N t f ⊗ₜ[ℂ] 1 := by
  atlas_forward_decl GlobalTheory.AnPer.isTay_apply_of_fn_eq_param
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

def slTayCoef {W : Opens (Tot I g)} (h : Hol W) (k : ℕ) (s : Fin k → I) (p : Tot Empty g) : ℂ :=
  (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 fun b ↦ Pi.single (s b) 1

theorem slTayCoef_analytic {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (h : Hol W) (k : ℕ) (s : Fin k → I) :
    AnalyticOnNhd ℂ (slTayCoef h k s) W₀ := fun p hp ↦ by
  have hA : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  have hG := (analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k (fun b ↦ Pi.single (s b) 1) hA).1
  exact analyticAt_const.mul (hG.comp analyticAt_snd)

def slTayHol {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (h : Hol W) (k : ℕ) (s : Fin k → I) : Hol W₀ :=
  Hol.mk (slTayCoef h k s) (slTayCoef_analytic hW h k s)

theorem isTay_expand {R : Type} [CommRing R] [Algebra ℂ R] {N : ℕ} {t : I → R} {W : Opens (Tot I g)}
    {W₀ : Opens (Tot Empty g)} (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W)
    {ρ : Hol W →+* R ⊗[ℂ] Hol W₀} (hρ : IsTay N t ρ) (h : Hol W) :
    ρ h = ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I, (∏ b, t (s b)) ⊗ₜ[ℂ] slTayHol hW h k s := by
  refine tensor_hol_ext_of_values W₀ R _ _ fun p hp ↦ ?_
  have e := hρ h p hp
  change evT R p hp (ρ h) = evT R p hp _
  rw [e, map_sum]
  unfold GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Hol.ev_apply, slTayHol, Hol.fn_mk _ _ hp,
    Algebra.smul_def, mul_comm]
  rfl

theorem dw_slTayHol {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (a : Fin g) (h : Hol W) (k : ℕ) (s : Fin k → I) :
    dw a (slTayHol hW h k s) = slTayHol hW (dw a h) k s := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hA : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  obtain ⟨hG, hD⟩ := analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k (fun b ↦ Pi.single (s b) 1) hA
  have e1 : slTayCoef h k s = (fun w : Fin g → ℂ ↦ (k.factorial : ℂ)⁻¹ *
      iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 fun b ↦ Pi.single (s b) 1) ∘ Prod.snd := rfl
  have hG' : DifferentiableAt ℂ (fun w : Fin g → ℂ ↦ (k.factorial : ℂ)⁻¹ *
      iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 fun b ↦ Pi.single (s b) 1) p.2 :=
    hG.differentiableAt.const_mul _
  have hev : (fun z : I → ℂ ↦ fderiv ℂ h.fn (z, p.2) ((0 : I → ℂ), Pi.single a 1)) =ᶠ[𝓝 0]
      fun z ↦ (dw a h).fn (z, p.2) := by
    have hc : Continuous fun z : I → ℂ ↦ ((z, p.2) : Tot I g) := continuous_id.prodMk continuous_const
    filter_upwards [hc.continuousAt.eventually_mem (W.isOpen.mem_nhds (hW p hp))] with z hz
    rw [dw, Hol.fn_der _ _ hz]
  rw [slTayHol, slTayHol, Hol.fn_mk _ _ hp, dw, Hol.fn_der _ _ hp,
    Hol.fderiv_fn_congr _ (F := slTayCoef h k s) (fun q hq ↦ Hol.fn_mk _ _ hq) hp, e1,
    fderiv_comp p hG' differentiableAt_snd, fderiv_snd,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', fderiv_const_mul hG.differentiableAt,
    ContinuousLinearMap.smul_apply, hD, smul_eq_mul]
  unfold slTayCoef
  congr 1
  exact (Filter.EventuallyEq.iteratedFDeriv ℂ hev k).eq_of_nhds ▸ rfl

theorem isTay_dw_lTensor : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h) := by
  intro I _ _ g R _ _ N t W W₀ hW ρ hρ a h
  rw [isTay_expand hW hρ (dw a h), isTay_expand hW hρ h, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [LinearMap.lTensor_tmul, ← dw_slTayHol hW a h k s]
  rfl

end GlobalTheory.AnPer
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParameterTaylorExpansionHom_fibreDerivation : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h) := by
  atlas_forward_decl GlobalTheory.AnPer.isTay_dw_lTensor
end

section
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

namespace GlobalTheory.AnPer.SliceZero

theorem prod_sumElim_zero {I : Type} {g : ℕ} {R : Type} [CommRing R] (N : ℕ) (t : I → R)
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (s : Fin (N + 1) → I ⊕ Fin g) :
    ∏ a, (Sum.elim t (0 : Fin g → R)) (s a) = 0 := by
  by_cases h : ∀ a, ∃ i, s a = Sum.inl i
  · choose f hf using h
    rw [Finset.prod_congr rfl fun a _ ↦ by rw [hf a]]
    simpa using ht f
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ : ∃ b, s a = Sum.inr b := by
      rcases hs : s a with i | b
      · exact absurd hs (ha i)
      · exact ⟨b, rfl⟩
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [hb]; rfl)

end GlobalTheory.AnPer.SliceZero

open GlobalTheory.AnPer.SliceZero in

theorem GlobalTheory.AnPer.exists_sliceZero_isTay : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∃ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ := by
  intro I _ _ g R _ _ N t ht W W₀ hW
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AnPer.exists_sliceTaylor_algHom N (Sum.elim t (0 : Fin g → R))
    (prod_sumElim_zero N t ht) (E := Tot Empty g) W W₀ Prod.snd
    (fun p _ ↦ analyticAt_snd) hW
  refine ⟨ρ.toRingHom, fun h p hp ↦ ?_⟩
  refine (hρ h p hp).trans ?_
  have hh : AnalyticAt ℂ h.fn (0, p.2 + (fun _ : I → ℂ ↦ (0 : Fin g → ℂ)) 0) := by
    rw [add_zero]; exact h.analytic _ (hW p hp)
  have hs := taylor_shear N t ht h.fn (fun _ ↦ (0 : Fin g → ℂ)) p.2 analyticAt_const hh
  simp only [add_zero, Pi.zero_apply, taylor_const_fun, map_zero, sub_zero] at hs
  rw [hs]
  rfl
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_isTay_of_slice_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∃ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ := by
  atlas_forward_decl GlobalTheory.AnPer.exists_sliceZero_isTay
end

section
open TopologicalSpace TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

section General

variable {R H : Type} [CommRing R] [Algebra ℂ R] [CommRing H] [Algebra ℂ H]

def redCoef (π : R →ₐ[ℂ] ℂ) : R ⊗[ℂ] H →ₐ[ℂ] H :=
  Algebra.TensorProduct.lift ((Algebra.ofId ℂ H).comp π) (AlgHom.id ℂ H) (fun _ _ ↦ Commute.all _ _)

theorem redCoef_tmul (π : R →ₐ[ℂ] ℂ) (d : R) (y : H) :
    redCoef π (d ⊗ₜ[ℂ] y) = algebraMap ℂ H (π d) * y := by
  simp [redCoef, Algebra.TensorProduct.lift_tmul]

theorem sub_redCoef_mem (π : R →ₐ[ℂ] ℂ) (x : R ⊗[ℂ] H) :
    x - 1 ⊗ₜ[ℂ] redCoef π x ∈
      (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] H) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d y =>
    rw [redCoef_tmul]
    have e : d ⊗ₜ[ℂ] y - (1 : R) ⊗ₜ[ℂ] (algebraMap ℂ H (π d) * y) =
        (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] H) (d - algebraMap ℂ R (π d)) * ((1 : R) ⊗ₜ[ℂ] y) := by
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, TensorProduct.smul_tmul]
    rw [e]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  | add x y hx hy =>
    have e : x + y - 1 ⊗ₜ[ℂ] redCoef π (x + y) = (x - 1 ⊗ₜ[ℂ] redCoef π x) + (y - 1 ⊗ₜ[ℂ] redCoef π y) := by
      rw [map_add, TensorProduct.tmul_add]; abel
    rw [e]; exact Ideal.add_mem _ hx hy

end General

theorem fn_redCoef {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {R : Type} [CommRing R]
    [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ) (x : R ⊗[ℂ] Hol W) {p : E} (hp : p ∈ W) :
    (redCoef π x).fn p = π (evT R p hp x) := by
  rw [← Hol.ev_apply p hp]
  change ((Hol.ev p hp).comp (redCoef π)) x = (π.comp (evT R p hp)) x
  congr 1
  refine Algebra.TensorProduct.ext' fun d y ↦ ?_
  simp only [AlgHom.comp_apply, redCoef_tmul, evT, Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.commutes,
    AlgHom.id_apply, Algebra.ofId_apply]
  simp

theorem taylor_red {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ)
    (t : I → R) (π : R →ₐ[ℂ] ℂ) (ht : ∀ i, π (t i) = 0) (f : (I → ℂ) → ℂ) :
    π (GlobalTheory.PeriodFamily.taylor N t f) = f 0 := by
  have h := GlobalTheory.PeriodFamily.taylor_sub_value_mem_span N t f
  have hle : Ideal.span (Set.range t) ≤ RingHom.ker π := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact ht i
  have := hle h
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
  simpa using this

theorem taylor_reduces_to_slice : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (π : R →ₐ[ℂ] ℂ), (∀ i, π (t i) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (h₀ : Hol W₀), (∀ p ∈ W₀, h₀.fn p = h.fn (0, p.2)) → ρ h - 1 ⊗ₜ[ℂ] h₀ ∈ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol W₀) := by
  intro I _ _ g R _ _ N t π ht W W₀ _ ρ hρ h h₀ hh₀
  have hq : redCoef π (ρ h) = h₀ := Hol.ext_fn fun p hp ↦ by
    rw [fn_redCoef π _ hp, hρ h p hp, taylor_red N t π ht, hh₀ p hp]
  have := sub_redCoef_mem (H := Hol W₀) π (ρ h)
  rwa [hq] at this

end GlobalTheory.AnPer
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_restriction_sub_mem_ideal_map : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (π : R →ₐ[ℂ] ℂ), (∀ i, π (t i) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (h₀ : Hol W₀), (∀ p ∈ W₀, h₀.fn p = h.fn (0, p.2)) → ρ h - 1 ⊗ₜ[ℂ] h₀ ∈ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol W₀) := by
  atlas_forward_decl GlobalTheory.AnPer.taylor_reduces_to_slice
end

section
section
set_option autoImplicit false

open Filter Topology TopologicalSpace

namespace GlobalTheory.AnPer.TaylorHom

open GlobalTheory.AnPer GlobalTheory.PeriodFamily

variable {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R]

theorem fn_add_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (f g : Hol V) :
    (f + g).fn =ᶠ[𝓝 0] fun z ↦ f.fn z + g.fn z := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_add f g hq

theorem fn_mul_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (f g : Hol V) :
    (f * g).fn =ᶠ[𝓝 0] fun z ↦ f.fn z * g.fn z := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_mul f g hq

theorem fn_algebraMap_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (c : ℂ) :
    (algebraMap ℂ (Hol V) c).fn =ᶠ[𝓝 0] fun _ ↦ c := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_algebraMap c hq

theorem taylor_algebraMap (N : ℕ) (t : I → R) {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (c : ℂ) :
    GlobalTheory.PeriodFamily.taylor N t (algebraMap ℂ (Hol V) c).fn = algebraMap ℂ R c := by
  rw [taylor_congr_germ N t _ _ (fn_algebraMap_eventually h0 c), taylor_const_fun]

noncomputable def taylorHom (N : ℕ) (t : I → R) (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0)
    (V : Opens (I → ℂ)) (h0 : (0 : I → ℂ) ∈ V) : Hol V →ₐ[ℂ] R where
  toFun f := GlobalTheory.PeriodFamily.taylor N t f.fn
  map_one' := by
    have h : (1 : Hol V) = algebraMap ℂ (Hol V) 1 := (map_one _).symm
    change GlobalTheory.PeriodFamily.taylor N t (1 : Hol V).fn = 1
    rw [h, taylor_algebraMap N t h0, map_one]
  map_mul' f g := by
    change GlobalTheory.PeriodFamily.taylor N t (f * g).fn = GlobalTheory.PeriodFamily.taylor N t f.fn * GlobalTheory.PeriodFamily.taylor N t g.fn
    rw [taylor_congr_germ N t _ _ (fn_mul_eventually h0 f g)]
    exact taylor_mul_of_prod_eq_zero N t ht _ _ (f.analytic 0 h0) (g.analytic 0 h0)
  map_zero' := by
    have h : (0 : Hol V) = algebraMap ℂ (Hol V) 0 := (map_zero _).symm
    change GlobalTheory.PeriodFamily.taylor N t (0 : Hol V).fn = 0
    rw [h, taylor_algebraMap N t h0, map_zero]
  map_add' f g := by
    change GlobalTheory.PeriodFamily.taylor N t (f + g).fn = GlobalTheory.PeriodFamily.taylor N t f.fn + GlobalTheory.PeriodFamily.taylor N t g.fn
    rw [taylor_congr_germ N t _ _ (fn_add_eventually h0 f g)]
    exact taylor_add_of_analyticAt N t _ _ (f.analytic 0 h0) (g.analytic 0 h0)
  commutes' c := taylor_algebraMap N t h0 c

end GlobalTheory.AnPer.TaylorHom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

theorem GlobalTheory.AnPer.exists_taylor_algHom : ∀ {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (V : Opens (I → ℂ)), 0 ∈ V → ∃ θ : Hol V →ₐ[ℂ] R, ∀ f, θ f = GlobalTheory.PeriodFamily.taylor N t f.fn := by
  intro I _ _ R _ _ N t ht V h0
  exact ⟨GlobalTheory.AnPer.TaylorHom.taylorHom N t ht V h0, fun f ↦ rfl⟩
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_taylor_algHom_holomorphic_nilpotent : ∀ {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (V : Opens (I → ℂ)), 0 ∈ V → ∃ θ : Hol V →ₐ[ℂ] R, ∀ f, θ f = taylor N t f.fn := by
  atlas_forward_decl GlobalTheory.AnPer.exists_taylor_algHom
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZero_move_tensor_holomorphic : ∀ {g : ℕ} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (ψ : R ⊗[ℂ] Hol W₀ →+* C) (n : Fin g → C), (∀ a b, n a * n b = 0) → ∃ ψ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (LinearMap.lTensor R (dw a).toLinearMap x) * n a := by
  first | exact @GlobalTheory.SqZeroMove.sqZeroMove | exact GlobalTheory.SqZeroMove.sqZeroMove | (intros; apply GlobalTheory.SqZeroMove.sqZeroMove <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CloseTen

theorem baseChange_tensor_holomorphic_closeness {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C)
    (ρ : Hol W →+* R ⊗[ℂ] Hol W₀)
    (hρ : ∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h))
    (ψ₂ : R ⊗[ℂ] Hol W₀ →+* C) (ρ₁ : Hol W₀ →+* C)
    (hc : Close J ρ₁ (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom)) :
    ∀ φ : R ⊗[ℂ] Hol W₀ →+* C,
      (∀ h : Hol W₀, φ ((1 : R) ⊗ₜ[ℂ] h) = ρ₁ h) →
      (∀ d : R, φ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (φ.comp ρ) (ψ₂.comp ρ) := by
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro φ hφ hφd
    have e : φ = ψ₂ := by
      apply RingHom.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul d h =>
        have e1 : d ⊗ₜ[ℂ] h = (d ⊗ₜ[ℂ] (1 : Hol W₀)) * ((1 : R) ⊗ₜ[ℂ] h) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
        rw [e1, map_mul, map_mul, hφd, hφ]
        rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    subst e
    exact Relation.ReflTransGen.refl
  | head hs _ ih =>
    intro φ hφ hφd
    obtain ⟨n, hnJ, hn2, hn⟩ := hs
    obtain ⟨φ', hφ'⟩ := GlobalTheory.T.exists_squareZero_move_tensor_holomorphic φ n hn2
    refine Relation.ReflTransGen.head ⟨n, hnJ, hn2, fun h => ?_⟩ (ih φ' (fun h => ?_) (fun d => ?_))
    · rw [RingHom.comp_apply, hφ']
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [RingHom.comp_apply, hρ]
    · rw [hφ', hn h, hφ]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, hφ]
    · rw [hφ', ← hφd]
      conv_rhs => rw [← add_zero (φ (d ⊗ₜ[ℂ] 1))]
      congr 1
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
        TensorProduct.tmul_zero, map_zero, zero_mul]

theorem close_tensor : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C) (ρ : Hol W →+* R ⊗[ℂ] Hol W₀), (∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h)) → ∀ ψ₁ ψ₂ : R ⊗[ℂ] Hol W₀ →+* C, (∀ d : R, ψ₁ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (ψ₁.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) → Close J (ψ₁.comp ρ) (ψ₂.comp ρ) := by
  intro I _ g W W₀ R _ _ C _ J ρ hρ ψ₁ ψ₂ hd hc
  exact baseChange_tensor_holomorphic_closeness J ρ hρ ψ₂ _ hc ψ₁ (fun h => rfl) hd

end GlobalTheory.CloseTen
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.close_comp_of_close_includeRight : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C) (ρ : Hol W →+* R ⊗[ℂ] Hol W₀), (∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h)) → ∀ ψ₁ ψ₂ : R ⊗[ℂ] Hol W₀ →+* C, (∀ d : R, ψ₁ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (ψ₁.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) → Close J (ψ₁.comp ρ) (ψ₂.comp ρ) := by
  atlas_forward_decl GlobalTheory.CloseTen.close_tensor
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem exists_tensorLift_of_DObj {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R]
    [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (S : K₀.DObj (et : Hol F₀.V →+* R) M) :
    ∃ ψ : R ⊗[ℂ] Hol (K₀.W S.T.k) →+* S.T.C, ∀ (d : R) (h : Hol (K₀.W S.T.k)),
      ψ (d ⊗ₜ[ℂ] h) = algebraMap R S.T.C d * S.T.ρ h := by
  letI : Algebra ℂ S.T.C := ((algebraMap R S.T.C).comp (algebraMap ℂ R)).toAlgebra
  let fR : R →ₐ[ℂ] S.T.C := { algebraMap R S.T.C with commutes' := fun _ ↦ rfl }
  let fH : Hol (K₀.W S.T.k) →ₐ[ℂ] S.T.C :=
    { S.T.ρ with
      commutes' := fun a ↦ by
        have h1 : algebraMap ℂ (Hol (K₀.W S.T.k)) a = K₀.cst S.T.k (algebraMap ℂ (Hol F₀.V) a) :=
          ((Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) (K₀.base S.T.k)).commutes a).symm
        change S.T.ρ (algebraMap ℂ (Hol (K₀.W S.T.k)) a) = algebraMap R S.T.C (algebraMap ℂ R a)
        rw [h1, S.T.ρ_cst, S.compat]
        change algebraMap R S.T.C (et (algebraMap ℂ (Hol F₀.V) a)) = _
        rw [et.commutes] }
  refine ⟨(Algebra.TensorProduct.lift fR fH (fun _ _ ↦ Commute.all _ _)).toRingHom, fun d h ↦ ?_⟩
  exact Algebra.TensorProduct.lift_tmul _ _ _ d h

end GlobalTheory.AnPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorLift_of_analyticThickening : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (S : K₀.DObj (et : Hol F₀.V →+* R) M), ∃ ψ : R ⊗[ℂ] Hol (K₀.W S.T.k) →+* S.T.C, ∀ (d : R) (h : Hol (K₀.W S.T.k)), ψ (d ⊗ₜ[ℂ] h) = algebraMap R S.T.C d * S.T.ρ h := by
  atlas_forward_decl GlobalTheory.AnPer.exists_tensorLift_of_DObj
end

section
section
open CategoryTheory TopologicalSpace TensorProduct
open GlobalTheory.AnPer

namespace GlobalTheory.AnPer

set_option maxHeartbeats 1000000 in

theorem exists_points_on_DObj : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (ρ : ∀ k, Hol (K.W (ka k)) →+* R ⊗[ℂ] Hol (K₀.W k)), (∀ k f, ρ k (K.cst (ka k) f) = θ f ⊗ₜ[ℂ] 1) → (∀ k a h, ρ k (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ k h)) → (∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k))) → ∀ (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)), (∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k))) → ∃ ρ' : ∀ S : K₀.DObj (et : Hol F₀.V →+* R) M, Hol (K.W (ka S.T.k)) →+* S.T.C, (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) ∧ (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) ∧ ∀ (S S' : K₀.DObj (et : Hol F₀.V →+* R) M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)) := by
  intro I _ g Λ _ F F₀ K K₀ R _ _ et M θ ka hka ρ hc hd hs res hr
  choose ψ hψ using GlobalTheory.T.exists_tensorLift_of_analyticThickening K₀ et M
  have h1 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (d : R), ψ S (d ⊗ₜ[ℂ] 1) = algebraMap R S.T.C d :=
    fun S d ↦ (hψ S d 1).trans (by rw [S.T.ρ.map_one, mul_one])
  have h2 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (h : Hol (K₀.W S.T.k)), ψ S (1 ⊗ₜ[ℂ] h) = S.T.ρ h :=
    fun S h ↦ (hψ S 1 h).trans (by rw [(algebraMap R S.T.C).map_one, one_mul])
  have hJ : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M),
      ∀ c ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)), ψ S c ∈ S.T.J := by
    intro S c hc
    have : M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)) ≤ S.T.J.comap (ψ S) := by
      refine Ideal.map_le_iff_le_comap.2 fun d hd ↦ ?_
      change ψ S (d ⊗ₜ[ℂ] 1) ∈ S.T.J
      rw [h1]
      exact S.mem d hd
    exact this hc
  refine ⟨fun S ↦ (ψ S).comp (ρ S.T.k), fun S f ↦ ?_, fun S h ↦ ?_, fun S S' f ↦ ?_⟩
  · exact (congrArg (ψ S) (hc _ f)).trans (h1 S _)
  · have := hJ S _ (hr S.T.k h)
    rw [(ψ S).map_sub, h2] at this
    exact this
  · have c1 := (hs _ _ _ (Charts.Hom.le f.1)).map (ψ S') (hJ S')
    have c2 := GlobalTheory.T.close_comp_of_close_includeRight S'.T.J (ρ S.T.k) (hd S.T.k)
      ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1))).toRingHom)
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S))
      (fun d ↦ by
        have e : Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1)) (d ⊗ₜ[ℂ] 1) = d ⊗ₜ[ℂ] 1 :=
          (Algebra.TensorProduct.map_tmul _ _ _ _).trans
            (congrArg (fun x ↦ d ⊗ₜ[ℂ] x) (Charts.shA (Charts.Hom.le f.1)).map_one)
        exact (congrArg (ψ S') e).trans ((h1 S' d).trans ((f.2 d).symm.trans (congrArg f.1.φ (h1 S d).symm))))
      (by
        have e1 : ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1))).toRingHom).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            S'.T.ρ.comp (Charts.sh (Charts.Hom.le f.1)) :=
          RingHom.ext fun h ↦ (congrArg (ψ S') (Algebra.TensorProduct.map_tmul (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1)) 1 h)).trans (h2 S' _)
        have e2 : ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S)).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            (f.1.φ : S.T.C →+* S'.T.C).comp S.T.ρ :=
          RingHom.ext fun h ↦ congrArg f.1.φ (h2 S h)
        rw [e1, e2]
        exact f.1.close)
    exact Relation.ReflTransGen.trans c1 c2

end GlobalTheory.AnPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_points_translationFamilyCharts_thickenings : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (ρ : ∀ k, Hol (K.W (ka k)) →+* R ⊗[ℂ] Hol (K₀.W k)), (∀ k f, ρ k (K.cst (ka k) f) = θ f ⊗ₜ[ℂ] 1) → (∀ k a h, ρ k (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ k h)) → (∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k))) → ∀ (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)), (∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k))) → ∃ ρ' : ∀ S : K₀.DObj (et : Hol F₀.V →+* R) M, Hol (K.W (ka S.T.k)) →+* S.T.C, (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) ∧ (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) ∧ ∀ (S S' : K₀.DObj (et : Hol F₀.V →+* R) M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)) := by
  atlas_forward_decl GlobalTheory.AnPer.exists_points_on_DObj
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GaussManinTaylor

theorem prod_zero_of_pow_eq_bot {R : Type} [CommRing R] (J : Ideal R) (n₀ : ℕ) (h : J ^ n₀ = ⊥) (N' : ℕ)
    (hN : n₀ ≤ N' + 1) (s : Fin (N' + 1) → R) (hs : ∀ a, s a ∈ J) : ∏ a, s a = 0 := by
  have h1 : ∏ a, s a ∈ ∏ _a ∈ (Finset.univ : Finset (Fin (N' + 1))), J := Ideal.prod_mem_prod (fun a _ ↦ hs a)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Ideal.pow_le_pow_right hN h1
  rw [h] at h2
  simpa using h2

end GlobalTheory.GaussManinTaylor

open GlobalTheory.GaussManinTaylor in
theorem GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B D : Type} [CommRing B] [CommRing D] [Algebra ℂ D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (u₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → 0 ∈ F.V → (∀ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, u₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (π : D →ₐ[ℂ] ℂ), IsNilpotent (RingHom.ker π) → ∀ {J : Ideal D} (dl : DividedPowers J), (∀ d ∈ J, π d = 0) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap (π : D →+* ℂ) → ∀ (n : IsMor (dp0 B) s dl s' j φ₀) (ψ : X₀ ⟶ X₀) (k : IsMor (dp0 ℂ) s₀ dl s' (algebraMap ℂ D) ψ), ψ = 𝟙 X₀ → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ {io : Type} (S : Finset io) (d : io → D) (a : io → FirstDeRham s₀) (p : io → Λ → ℂ) (p' : io → (Λ →+ Hol F₀.V)), (∀ i l, p' i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod u₀ (a i) (p' i)) → n.pull1 c = ∑ i ∈ S, d i • k.pull1 (a i) → ∀ l, ∑ i ∈ S, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn := by
  intro I _ _ g Λ _ F F₀ B D _ _ _ X X₀ s s₀ σ e u₀ hX hX₀ h0V hV₀ hτ φ₀ hφ₀ π hπ J dl hJ N t ht hprod j hj s' hs' n ψ kk hψ c per hper ιo S d a p p' hp' hpa hsum l

  obtain ⟨R, _, _, io, π', m, hinj, hπ', hnil, hm0, hmm, hmsum⟩ :=
    GlobalTheory.SquareZeroSum.exists_sum_sq_zero N D π t hπ ht hprod
  set t' : I → R := fun i ↦ ∑ j, m j i with ht'def
  have ht' : (fun i ↦ io (t i)) = t' := funext hmsum
  have hprod' : ∀ s : Fin (N + 1) → I, ∏ a, t' (s a) = 0 := by
    intro s
    rw [← ht']
    simp only
    rw [← map_prod, hprod, map_zero]
  obtain ⟨n₀, hn₀⟩ := hnil
  set N' := N + n₀ with hN'
  have hker : ∀ s : Fin (N' + 1) → R, (∀ a, s a ∈ RingHom.ker (π' : R →+* ℂ)) → ∏ a, s a = 0 :=
    fun s hs ↦ prod_zero_of_pow_eq_bot _ n₀ hn₀ N' (by omega) s hs
  have ht'ker : ∀ i, t' i ∈ RingHom.ker (π' : R →+* ℂ) := fun i ↦ by
    have h1 : io (t i) = t' i := congrFun ht' i
    rw [RingHom.mem_ker, ← h1]
    change π' (io (t i)) = 0
    rw [hπ', ht]
  have hprodN' : ∀ s : Fin (N' + 1) → I, ∏ a, t' (s a) = 0 := fun s ↦ hker _ fun a ↦ ht'ker (s a)

  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_taylor_algHom_holomorphic_nilpotent N' t' hprodN' F.V h0V
  have hθio : ∀ f : Hol F.V, θ f = io (GlobalTheory.PeriodFamily.taylor N t f.fn) := by
    intro f
    rw [hθ, GlobalTheory.PeriodFamily.taylor_eq_of_le N t' hprod' N' (by omega),
      (GlobalTheory.PeriodFamily.taylor_formal_properties N t).2.2.2.2.1 R io f.fn, ht']

  have hdef : (default : Empty → ℂ) ∈ F₀.V := hV₀ _
  obtain ⟨K₀, K, ka, hRich, hU₀, hU, hmemk, hka⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map u₀ e (fun _ ↦ (0 : I → ℂ))
    (fun _ _ ↦ analyticAt_const) (fun _ _ ↦ h0V) (LinearMap.id) (AddMonoidHom.id Λ)
    (fun l z _ ↦ (hτ l z).symm)
  have hmem0 : ∀ k, ∀ q ∈ K₀.W k, (((0 : I → ℂ), q.2) : Tot I g) ∈ K.W (ka k) := fun k q hq ↦ hmemk k q hq
  have hka' : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k) := fun h ↦ hka _ _ _ h
  obtain ⟨r₀, hr₀, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine u₀ hX₀ K₀ hU₀
  obtain ⟨r, hr, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine e hX K hU
  have han : AnalyticOnNhd ℂ (fun q : Tot Empty g ↦ (((0 : I → ℂ), q.2) : Tot I g)) ⊤ :=
    fun _ _ ↦ analyticAt_const.prod analyticAt_snd
  let res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k) := fun k ↦
    (Hol.comap (fun q : Tot Empty g ↦ (((0 : I → ℂ), q.2) : Tot I g)) (fun q _ ↦ han q trivial) (hmem0 k)).toRingHom
  have hres : ∀ k (h : Hol (K.W (ka k))) {q : Tot Empty g}, q ∈ K₀.W k → (res k h).fn q = h.fn ((0 : I → ℂ), q.2) :=
    fun k h q hq ↦ Hol.fn_comap _ _ _ h hq

  choose ρ hρ using fun k ↦ GlobalTheory.T.exists_ringHom_isTay_of_slice_zero N' t' hprodN' (K.W (ka k)) (K₀.W k) (hmem0 k)
  let M : Ideal R := RingHom.ker (π' : R →+* ℂ)
  let et : Hol F₀.V →ₐ[ℂ] R := (Algebra.ofId ℂ R).comp (Hol.ev default hdef)
  have hcst : ∀ k f, ρ k (K.cst (ka k) f) = θ.toRingHom f ⊗ₜ[ℂ] 1 := fun k f ↦ by
    rw [GlobalTheory.T.isParameterTaylorExpansionHom_apply_of_param_only N' t' _ _ (hmem0 k) (ρ k) (hρ k) _ f.fn (fun q hq ↦ Charts.fn_cst _ _ _ hq)]
    exact congrArg (· ⊗ₜ[ℂ] (1 : Hol (K₀.W k))) (hθ f).symm
  have hdw : ∀ k a h, ρ k (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ k h) := fun k a h ↦
    GlobalTheory.T.isParameterTaylorExpansionHom_fibreDerivation N' t' _ _ (hmem0 k) (ρ k) (hρ k) a h
  have hclose : ∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka' h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k)) := by
    intro l k' k h
    have hρk := hρ k
    have hρk' := hρ k'
    rw [ht'def] at hρk hρk'
    exact GlobalTheory.T.close_taylor_shift_alt K K₀ M N' hker N m (fun j i ↦ hm0 j i) hmm hτ l (ka k) (ka k') k k' (hka' h) h (hmem0 k') (ρ k) (ρ k') hρk hρk'
  have hred : ∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k)) :=
    fun k h ↦ GlobalTheory.T.taylor_restriction_sub_mem_ideal_map N' t' π' (fun i ↦ ht'ker i) _ _ (hmem0 k) (ρ k) (hρ k) h (res k h) (fun q hq ↦ hres k h hq)
  obtain ⟨ρ', hρ'1, hρ'2, hρ'3⟩ := GlobalTheory.T.exists_points_translationFamilyCharts_thickenings K K₀ et M θ.toRingHom ka hka' ρ hcst hdw hclose res hred
  have hetc : ∀ x : ℂ, et (algebraMap ℂ (Hol F₀.V) x) = algebraMap ℂ R x := fun x ↦ et.commutes x
  have H : IsOver (et : Hol F₀.V →+* R) M s₀ (algebraMap ℂ (Hol F₀.V)) J s' (π : D →+* ℂ) (io : D →+* R) :=
    { w := hs'
      mem := fun d hd ↦ by
        rw [RingHom.mem_ker]
        change π' (io d) = 0
        rw [hπ', hJ d hd]
      red := fun d ↦ by
        rw [RingHom.mem_ker, map_sub]
        change π' (io d) - π' (et (algebraMap ℂ (Hol F₀.V) (π d))) = 0
        rw [hetc, AlgHom.commutes, hπ']
        simp }
  have hpt : ∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀ := fun k ↦ by
    refine GlobalTheory.T.holomorphicPoint_ext_of_isSeparated (K₀.W k) hX _ _ (fun q hq ↦ ?_)
    have hq' := hmem0 k q hq
    have hev : (Hol.ev q hq).toRingHom.comp (res k) = (Hol.ev (((0 : I → ℂ), q.2) : Tot I g) hq').toRingHom :=
      RingHom.ext fun h ↦ by
        change Hol.ev q hq (res k h) = Hol.ev _ hq' h
        rw [Hol.ev_apply, Hol.ev_apply, hres k h hq]
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, hev, hr (ka k) _ hq', ← Category.assoc, hr₀ k q hq, hφ₀ q]
  have hθj : ∀ b, θ.toRingHom (σ b) = io (j b) := fun b ↦ by
    rw [hj]
    exact hθio (σ b)
  have hfam := GlobalTheory.T.period_over_ring_restrict_family_class K K₀ (et : Hol F₀.V →+* R) M θ.toRingHom ka hka' res ρ' hρ'1 hρ'2 hρ'3 r r₀ dl H j φ₀ n hθj hpt c per (hper K r hr)
  have hfib : ∀ i, (r₀.coefD dl H).pull1 (kk.pull1 (a i)) = K₀.perClD (et : Hol F₀.V →+* R) M ((et : Hol F₀.V →+* R).toAddMonoidHom.comp (p' i)) :=
    fun i ↦ GlobalTheory.T.coefD_pull1_eq_perClD_of_pull1_eq_perCl K₀ (et : Hol F₀.V →+* R) M r₀ dl H (algebraMap ℂ D) ψ kk hψ
      (fun b ↦ by
        change et (algebraMap ℂ (Hol F₀.V) b) = io (algebraMap ℂ D b)
        rw [hetc, AlgHom.commutes]) (a i) (p' i) (hpa i K₀ r₀ hr₀)
  have hmain := congrArg (r₀.coefD dl H).pull1 hsum
  rw [hfam, map_sum] at hmain
  simp only [map_smulₛₗ, hfib] at hmain
  have het : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, (et : Hol F₀.V →+* R) f = algebraMap ℂ R (f.fn z) := fun f z hz ↦ by
    have : z = default := Subsingleton.elim _ _
    subst this
    change algebraMap ℂ R (Hol.ev default hdef f) = _
    rw [Hol.ev_apply]
  have hdu := GlobalTheory.T.periodClass_linear_relation_unique_of_nilpotent K₀ (et : Hol F₀.V →+* R) M hRich hV₀ ⟨n₀, hn₀⟩ het S _ _ _ hmain l
  apply hinj
  rw [map_sum, ← hθio]
  refine Eq.trans ?_ hdu.symm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change io (d i * algebraMap ℂ D (p i l)) = io (d i) * et (p' i l)
  rw [map_mul, AlgHom.commutes, hp', hetc]
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_period_eq_period_over_thickening_alt : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B D : Type} [CommRing B] [CommRing D] [Algebra ℂ D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (u₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → 0 ∈ F.V → (∀ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, u₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (π : D →ₐ[ℂ] ℂ), IsNilpotent (RingHom.ker π) → ∀ {J : Ideal D} (dl : DividedPowers J), (∀ d ∈ J, π d = 0) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap (π : D →+* ℂ) → ∀ (n : IsMor (dp0 B) s dl s' j φ₀) (ψ : X₀ ⟶ X₀) (k : IsMor (dp0 ℂ) s₀ dl s' (algebraMap ℂ D) ψ), ψ = 𝟙 X₀ → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ {io : Type} (S : Finset io) (d : io → D) (a : io → FirstDeRham s₀) (p : io → Λ → ℂ) (p' : io → (Λ →+ Hol F₀.V)), (∀ i l, p' i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod u₀ (a i) (p' i)) → n.pull1 c = ∑ i ∈ S, d i • k.pull1 (a i) → ∀ l, ∑ i ∈ S, d i * algebraMap ℂ D (p i l) = taylor N t (per l).fn := by
  atlas_forward_decl GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening
end
