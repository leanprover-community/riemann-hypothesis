module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ExistsDpPow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso

noncomputable section

namespace GlobalTheory.CompanionTheory.DisoHm

section Lift
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'}

end Lift

section Scal
variable {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

variable {L}

end Scal

section G
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

end G

section Gen
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem IdF.ext' {a b : IdF A} (h : ∀ T, a.S T = b.S T) : a = b := by
  cases a
  cases b
  congr
  exact funext h

theorem idM_bij {R' : Type} [CommRing R'] {σ : R →+* R'} {F : C ⥤ ModuleCat.{0} R} {F' : C ⥤ ModuleCat.{0} R'}
    (τ : ∀ T, F.obj T →ₛₗ[σ] F'.obj T)
    (nat : ∀ {T T' : C} (φ : T ⟶ T') (x : F.obj T), τ T' ((F.map φ).hom x) = (F'.map φ).hom (τ T x))
    (h : ∀ T, Function.Bijective (τ T)) (j : ℕ) :
    Function.Bijective ((⟨𝟭 C, τ, nat⟩ : CH.Mor F F' σ).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij _ (fun n => ⟨fun x y hxy => ?_, fun y => ?_⟩) j
  · funext s
    refine (h _).1 ?_
    have := congrFun hxy s
    exact this
  · exact ⟨fun s => Function.surjInv (h _).2 (y s), funext fun s => Function.surjInv_eq (h _).2 (y s)⟩

theorem sqLe_bij {a b a' b' : IdF A} (ha : ∀ T, a.S T = a'.S T) (hb : ∀ T, b.S T = b'.S T) (j : ℕ) :
    Function.Bijective ((sqLe (a := a) (b := b) (a' := a') (b' := b') (fun T => (ha T).le) (fun T => (hb T).le)).pull j) := by
  obtain rfl : a = a' := IdF.ext' ha
  obtain rfl : b = b' := IdF.ext' hb
  refine idM_bij (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).τ
    (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).nat (fun T => ?_) j
  have e : (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).τ T = LinearMap.id := by
    ext ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [e]
  exact Function.bijective_id
end Gen

section Lk
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

end Lk
end GlobalTheory.CompanionTheory.DisoHm

namespace GlobalTheory.CompanionTheory.DisoHm
section Cover
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R}

def smulM (m : CH.Mor F F' (RingHom.id R)) (n : R) : CH.Mor F F' (RingHom.id R) where
  G := m.G
  τ T := n • m.τ T
  nat φ x := by
    change n • m.τ _ _ = (F'.map φ).hom (n • m.τ _ x)
    rw [m.nat, map_smul]

theorem smulM_pull (m : CH.Mor F F' (RingHom.id R)) (n : R) (j : ℕ) (x : CH.H F j) :
    (smulM m n).pull j x = n • m.pull j x := by
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  rfl

theorem tens_iff {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') :
    Tens R (N := fun _ : Unit => R) (M := fun _ => M) (M' := M') (fun _ n x => n • f x) ↔ Function.Bijective f := by
  let e : (∀ _ : Unit, R ⊗[R] M) ≃+ M :=
    (AddEquiv.piUnique (fun _ : Unit => R ⊗[R] M)).trans (TensorProduct.lid R M).toAddEquiv
  have he : ∀ n x, e (Pi.single () (n ⊗ₜ x)) = n • x := fun n x => by simp [e]
  constructor
  · rintro ⟨g, hg⟩
    have : ∀ x, f x = g (e.symm x) := fun x => by
      have h2 : g (Pi.single () ((1 : R) ⊗ₜ x)) = f x := (hg () 1 x).trans (one_smul _ _)
      have h3 : e.symm x = Pi.single () ((1 : R) ⊗ₜ x) := by
        refine (AddEquiv.symm_apply_eq e).2 ?_
        rw [he, one_smul]
      rw [h3, h2]
    have e2 : (f : M → M') = (e.symm.trans g) := funext this
    rw [e2]
    exact (e.symm.trans g).bijective
  · intro hf
    refine ⟨e.trans (AddEquiv.ofBijective f.toAddMonoidHom hf), fun _ n x => ?_⟩
    change f (e _) = _
    rw [he, map_smul]

theorem cover_bij (m : CH.Mor F F' (RingHom.id R)) {A : Type} [Fintype A] (U : A → ObjectProperty C)
    (U' : A → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hU' : ∀ α, Cosieve (U' α)) (hc : ∀ T, ∃ α, U α T)
    (hc' : ∀ T, ∃ α, U' α T) (h : ∀ α T, U' α T → U α (m.G.obj T))
    (H : ∀ S : Finset A, S.Nonempty → ∀ j, Function.Bijective
      ((morU m (U := capS U S) (U' := capS U' S) fun T hT α hα => h α T (hT α hα)).pull j)) (j : ℕ) :
    Function.Bijective (m.pull j) := by
  have key := GlobalTheory.CompanionTheory.CosieveBC.base_change_of_cover (σ := RingHom.id R) m.G (ι := Unit) (fun _ => R) (fun _ => F) F'
    (fun _ n T => (smulM m n).τ T) (fun _ n _ _ φ x => (smulM m n).nat φ x)
    (fun _ n n' T x => by simp [smulM, add_smul]) (fun _ r n T x => by simp [smulM, mul_smul])
    U U' hU hU' hc hc' h (fun S hS j => ?_) j
  · obtain ⟨g, hg⟩ := key
    exact (tens_iff (m.pull j)).1 ⟨g, fun i n x => (hg i n x).trans (smulM_pull m n j x)⟩
  · obtain ⟨g, hg⟩ := (tens_iff ((morU m (U := capS U S) (U' := capS U' S) fun T hT α hα => h α T (hT α hα)).pull j)).2 (H S hS j)
    refine ⟨g, fun i n x => (hg i n x).trans ?_⟩
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
end Cover
end GlobalTheory.CompanionTheory.DisoHm

namespace GlobalTheory.CompanionTheory.DisoHm
section Ch
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

end Ch
end GlobalTheory.CompanionTheory.DisoHm
