import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated

section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GroundTheory.Arith.SchemeCoh (inter inter_le_comp)

namespace UpperTheory.Gal.DifferentialFormSections

variable {K : Type} [CommRing K]

abbrev Fm (K A : Type) [CommRing K] [CommRing A] [Algebra K A] : Type := ExteriorAlgebra A Ω[A⁄K]

section
variable {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

def dd (K : Type) [CommRing K] [Algebra K A] (a : A) : Fm K A := ExteriorAlgebra.ι A (KaehlerDifferential.D K A a)

def fmMap (φ : A →ₐ[K] B) : Fm K A →ₐ[K] Fm K B :=
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  (ExteriorAlgebra.lift A ⟨((ExteriorAlgebra.ι B).restrictScalars A) ∘ₗ KaehlerDifferential.map K K A B,
    fun _ => ExteriorAlgebra.ι_sq_zero _⟩).restrictScalars K

def dlog (K : Type) [CommRing K] [Algebra K A] (u : Aˣ) : Fm K A := (↑u⁻¹ : A) • dd K (u : A)

def sgn (n : ℕ) : Fm K A →ₗ[K] Fm K A :=
  (((CliffordAlgebra.involute (Q := (0 : QuadraticForm A Ω[A⁄K]))) ^ n : _ →ₐ[A] _).toLinearMap).restrictScalars K
end

abbrev Sch (K : Type) [CommRing K] : Type 1 := Over (Spec (CommRingCat.of K))

def Sec (X : Sch K) (U : X.left.Opens) : Type := Γ(X.left, U)

instance (X : Sch K) (U : X.left.Opens) : CommRing (Sec X U) := inferInstanceAs (CommRing Γ(X.left, U))

instance (X : Sch K) (U : X.left.Opens) : Algebra K (Sec X U) :=
  (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Scheme.Hom.appLE X.hom ⊤ U le_top).hom : K →+* Γ(X.left, U)).toAlgebra

def secMap {X Y : Sch K} (f : Y ⟶ X) {U : X.left.Opens} {V : Y.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U) : Sec X U →ₐ[K] Sec Y V where
  toRingHom := (Scheme.Hom.appLE f.left U V h).hom
  commutes' r := by
    have e : Scheme.Hom.appLE X.hom ⊤ U le_top ≫ Scheme.Hom.appLE f.left U V h = Scheme.Hom.appLE Y.hom ⊤ V le_top := by
      refine (Scheme.Hom.appLE_comp_appLE f.left X.hom ⊤ U V le_top h).trans ?_
      have e2 := Over.w f
      revert e2
      generalize Y.hom = g
      rintro rfl
      rfl
    exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom r)) e

def secRes (X : Sch K) {U V : X.left.Opens} (h : V ≤ U) : Sec X U →ₐ[K] Sec X V := secMap (𝟙 X) h

variable {X Y : Sch K} {ι κ : Type}

abbrev cap (U : ι → X.left.Opens) {n : ℕ} (i : Fin n → ι) : X.left.Opens := inter (X := X.left.toTopCat) U i

abbrev Co (U : ι → X.left.Opens) (n : ℕ) : Type := ∀ i : Fin (n + 1) → ι, Fm K (Sec X (cap U i))

def dC (U : ι → X.left.Opens) (n : ℕ) : Co U n →ₗ[K] Co U (n + 1) :=
  LinearMap.pi fun i => ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    ((fmMap (secRes X (inter_le_comp (X := X.left.toTopCat) U i k.succAbove))).toLinearMap ∘ₗ LinearMap.proj (i ∘ k.succAbove))

def Bd (U : ι → X.left.Opens) : (n : ℕ) → Submodule K (Co U n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (dC U n)

abbrev HC (U : ι → X.left.Opens) (n : ℕ) : Type := LinearMap.ker (dC U n) ⧸ (Bd U n).submoduleOf (LinearMap.ker (dC U n))

open Classical in

def cls {U : ι → X.left.Opens} {n : ℕ} (σ : Co U n) : HC U n :=
  if h : dC U n σ = 0 then Submodule.Quotient.mk ⟨σ, h⟩ else 0

def rep {U : ι → X.left.Opens} {n : ℕ} (x : HC U n) : Co U n := (Quotient.out x).1

def cupC {U : ι → X.left.Opens} {a b n : ℕ} (h : a + b = n) (σ : Co U a) (τ : Co U b) : Co U n := fun i =>
  fmMap (secRes X (inter_le_comp (X := X.left.toTopCat) U i fun s : Fin (a + 1) => ⟨s, by omega⟩)) (sgn b (σ _)) *
    fmMap (secRes X (inter_le_comp (X := X.left.toTopCat) U i fun s : Fin (b + 1) => ⟨a + s, by omega⟩)) (τ _)

def cupH {U : ι → X.left.Opens} {a b n : ℕ} (h : a + b = n) (x : HC U a) (y : HC U b) : HC U n := cls (cupC h (rep x) (rep y))

theorem cap_le (f : Y ⟶ X) {U : ι → X.left.Opens} {V : κ → Y.left.Opens} (t : κ → ι) (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j))
    {n : ℕ} (j : Fin n → κ) : cap V j ≤ f.left ⁻¹ᵁ cap U (t ∘ j) := fun x hx =>
  (GroundTheory.Arith.SchemeCoh.mem_inter_iff (X := X.left.toTopCat) (U := U) (t ∘ j) _).2 fun a =>
    ht (j a) ((GroundTheory.Arith.SchemeCoh.mem_inter_iff (X := Y.left.toTopCat) (U := V) j x).1 hx a)

def pullC (f : Y ⟶ X) {U : ι → X.left.Opens} {V : κ → Y.left.Opens} (t : κ → ι) (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j)) (n : ℕ) :
    Co U n →ₗ[K] Co V n :=
  LinearMap.pi fun j => (fmMap (secMap f (cap_le f t ht j))).toLinearMap ∘ₗ LinearMap.proj (t ∘ j)

def pullHC (f : Y ⟶ X) {U : ι → X.left.Opens} {V : κ → Y.left.Opens} (t : κ → ι) (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j)) {n : ℕ}
    (x : HC U n) : HC V n := cls (pullC f t ht n (rep x))

abbrev all (X : Sch K) : X.left.affineOpens → X.left.Opens := Subtype.val

abbrev H (X : Sch K) (n : ℕ) : Type := HC (all X) n

def deg (U : ι → X.left.Opens) (a n : ℕ) : Submodule K (HC U n) :=
  Submodule.span K {x | ∃ σ : Co U n, (∀ i, σ i ∈ ⋀[Sec X (cap U i)]^a Ω[Sec X (cap U i)⁄K]) ∧ dC U n σ = 0 ∧ x = cls σ}

abbrev Hd (X : Sch K) (a n : ℕ) : Submodule K (H X n) := deg (all X) a n

structure IsCov (U : ι → X.left.Opens) : Prop where
  aff : ∀ i, IsAffineOpen (U i)
  cov : iSup U = ⊤

def down {U : ι → X.left.Opens} (hU : IsCov U) {n : ℕ} (x : H X n) : HC U n :=
  pullHC (𝟙 X) (U := all X) (V := U) (fun i => (⟨U i, hU.aff i⟩ : X.left.affineOpens)) (fun _ _ hx => hx) x

def up {U : ι → X.left.Opens} (hU : IsCov U) {n : ℕ} (y : HC U n) : H X n := Function.invFun (down hU) y

def Pr (f : Y ⟶ X) : Type := {p : Y.left.affineOpens × X.left.affineOpens // p.1.1 ≤ f.left ⁻¹ᵁ p.2.1}

theorem isCov_pr (f : Y ⟶ X) : IsCov fun p : Pr f => p.1.1.1 where
  aff p := p.1.1.2
  cov := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.left y)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hy', hVU⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ (f.left ⁻¹ᵁ U : Y.left.Opens) from hy) (f.left ⁻¹ᵁ U).2
    exact Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, ⟨U, hU⟩), hVU⟩, hy'⟩

def pull (f : Y ⟶ X) {n : ℕ} (x : H X n) : H Y n := up (isCov_pr f) (pullHC f (fun p : Pr f => p.1.2) (fun p => p.2) x)

abbrev cup {a b n : ℕ} (h : a + b = n) (x : H X a) (y : H X b) : H X n := cupH h x y

def one (X : Sch K) : H X 0 := cls fun _ => 1

structure Coc (X : Sch K) : Type 1 where
  ι : Type
  U : ι → X.left.Opens
  cov : IsCov U
  g : ∀ i : Fin 2 → ι, (Sec X (cap U i))ˣ
  coc : ∀ i : Fin 3 → ι,
    secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 2)) (g (i ∘ Fin.succAbove 2)).val *
      secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 0)) (g (i ∘ Fin.succAbove 0)).val =
      secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 1)) (g (i ∘ Fin.succAbove 1)).val

def c1 (L : Coc X) : H X 1 := up L.cov (cls fun i => dlog K (L.g i))

def Coc.triv (X : Sch K) : Coc X where
  ι := X.left.affineOpens
  U := all X
  cov := ⟨fun i => i.2, iSup_affineOpens_eq_top _⟩
  g _ := 1
  coc _ := by simp only [Units.val_one, map_one, mul_one]

end UpperTheory.Gal.DifferentialFormSections
end
end

section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GroundTheory.Arith.SchemeCoh

namespace UpperTheory.Gal.DifferentialFormSections

def FmLaws : Prop := ∀ (K : Type) [CommRing K],
  (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B),
    (∀ a, fmMap φ (algebraMap A _ a) = algebraMap B _ (φ a)) ∧ (∀ a, fmMap φ (dd K a) = dd K (φ a)) ∧
    (∀ n x, fmMap φ (sgn n x) = sgn n (fmMap φ x)) ∧ (∀ (u : Aˣ), fmMap φ (dlog K u) = dlog K (Units.map φ.toMonoidHom u)) ∧
    (∀ (a : ℕ), ∀ x ∈ ⋀[A]^a Ω[A⁄K], fmMap φ x ∈ ⋀[B]^a Ω[B⁄K]) ∧ (Function.Surjective φ → Function.Surjective (fmMap φ)) ∧
    (∀ F G : Fm K A →ₐ[K] Fm K B, (∀ a, F (algebraMap A _ a) = G (algebraMap A _ a)) → (∀ a, F (dd K a) = G (dd K a)) → F = G) ∧
    ∀ (C : Type) [CommRing C] [Algebra K C] (ψ : B →ₐ[K] C) (x : Fm K A), fmMap ψ (fmMap φ x) = fmMap (ψ.comp φ) x) ∧
  (∀ (A : Type) [CommRing A] [Algebra K A], (∀ x : Fm K A, fmMap (AlgHom.id K A) x = x) ∧
    (∀ u v : Aˣ, dlog K (u * v) = dlog K u + dlog K v) ∧ (∀ (n : ℕ) (x y : Fm K A), sgn n (x * y) = sgn n x * sgn n y) ∧
    (∀ (m n : ℕ) (x : Fm K A), sgn m (sgn n x) = sgn (m + n) x) ∧ (∀ x : Fm K A, sgn 0 x = x) ∧ (∀ n, sgn n (1 : Fm K A) = 1) ∧
    ∀ (n a : ℕ), ∀ x ∈ ⋀[A]^a Ω[A⁄K], sgn (K := K) n x = ((-1 : ℤ) ^ (n * a)) • x) ∧
  (∀ (X : Sch K) (U : X.left.Opens) (h : U ≤ U), secRes X h = AlgHom.id K _) ∧
  ∀ {X Y Z : Sch K} (f : Y ⟶ X) (g : Z ⟶ Y) {U : X.left.Opens} {V : Y.left.Opens} {W : Z.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U)
    (h' : W ≤ g.left ⁻¹ᵁ V) (h'' : W ≤ (g ≫ f).left ⁻¹ᵁ U), (secMap g h').comp (secMap f h) = secMap (g ≫ f) h''

def ClsLaws : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (ι : Type) (U : ι → X.left.Opens) (n : ℕ),
  (∀ σ : Co U n, dC U (n + 1) (dC U n σ) = 0) ∧ (∀ x : HC U n, dC U n (rep x) = 0 ∧ cls (rep x) = x) ∧
  (∀ σ τ : Co U n, dC U n σ = 0 → dC U n τ = 0 → (cls σ = cls τ ↔ σ - τ ∈ Bd U n) ∧ cls (σ + τ) = cls σ + cls τ) ∧
  (∀ (c : K) (σ : Co U n), dC U n σ = 0 → cls (c • σ) = c • cls σ) ∧ cls (0 : Co U n) = 0

def CupCLaws : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (ι : Type) (U : ι → X.left.Opens) (a b n : ℕ) (h : a + b = n),
  (∀ (σ σ' : Co U a) (τ : Co U b), cupC h (σ + σ') τ = cupC h σ τ + cupC h σ' τ) ∧
  (∀ (σ : Co U a) (τ τ' : Co U b), cupC h σ (τ + τ') = cupC h σ τ + cupC h σ τ') ∧
  (∀ (c : K) (σ : Co U a) (τ : Co U b), cupC h (c • σ) τ = c • cupC h σ τ ∧ cupC h σ (c • τ) = c • cupC h σ τ) ∧
  (∀ (σ : Co U a) (τ : Co U b), dC U n (cupC h σ τ) = cupC (by omega : a + 1 + b = n + 1) (dC U a σ) τ +
    ((-1 : ℤ) ^ a) • cupC (by omega : a + (b + 1) = n + 1) (fun i => sgn 1 (σ i)) (dC U b τ)) ∧
  (∀ σ : Co U a, dC U a (fun i => sgn 1 (σ i)) = fun i => sgn 1 (dC U a σ i)) ∧
  ∀ (c m k : ℕ) (h₁ : n + c = m) (h₂ : b + c = k) (h₃ : a + k = m) (σ : Co U a) (τ : Co U b) (ρ : Co U c),
    cupC h₁ (cupC h σ τ) ρ = cupC h₃ σ (cupC h₂ τ ρ)

def CupLaws : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (ι : Type) (U : ι → X.left.Opens) (a b n : ℕ) (h : a + b = n),
  (∀ (σ : Co U a) (τ : Co U b), dC U a σ = 0 → dC U b τ = 0 → dC U n (cupC h σ τ) = 0 ∧ cupH h (cls σ) (cls τ) = cls (cupC h σ τ)) ∧
  (∀ (x x' : HC U a) (y : HC U b), cupH h (x + x') y = cupH h x y + cupH h x' y) ∧
  (∀ (x : HC U a) (y y' : HC U b), cupH h x (y + y') = cupH h x y + cupH h x y') ∧
  (∀ (c : K) (x : HC U a) (y : HC U b), cupH h (c • x) y = c • cupH h x y ∧ cupH h x (c • y) = c • cupH h x y) ∧
  (∀ x : HC U a, cupH (zero_add a) (cls fun _ => 1) x = x ∧ cupH (add_zero a) x (cls fun _ => 1) = x) ∧
  (∀ (c m k : ℕ) (h₁ : n + c = m) (h₂ : b + c = k) (h₃ : a + k = m) (x : HC U a) (y : HC U b) (z : HC U c),
    cupH h₁ (cupH h x y) z = cupH h₃ x (cupH h₂ y z)) ∧
  ∀ (r s : ℕ), ∀ x ∈ deg U r a, ∀ y ∈ deg U s b, cupH h x y ∈ deg U (r + s) n

def CupComm : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (ι : Type) (U : ι → X.left.Opens) (a b n : ℕ) (h : a + b = n)
  (h' : b + a = n) (r s : ℕ), ∀ x ∈ deg U r a, ∀ y ∈ deg U s b, cupH h x y = ((-1 : ℤ) ^ ((r + a) * (s + b))) • cupH h' y x

def PullCLaws : Prop := ∀ (K : Type) [CommRing K] {X Y : Sch K} (f : Y ⟶ X) (ι κ : Type) (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (t : κ → ι) (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j)) (n : ℕ),
  (∀ σ : Co U n, dC V n (pullC f t ht n σ) = pullC f t ht (n + 1) (dC U n σ)) ∧
  (∀ σ : Co U n, dC U n σ = 0 → pullHC f t ht (cls σ) = cls (pullC f t ht n σ)) ∧ IsLinearMap K (pullHC f t ht (n := n)) ∧
  (∀ (a b : ℕ) (h : a + b = n) (x : HC U a) (y : HC U b), pullHC f t ht (cupH h x y) = cupH h (pullHC f t ht x) (pullHC f t ht y)) ∧
  pullHC f t ht (cls (n := 0) fun _ => 1) = cls (fun _ => 1) ∧ (∀ a, ∀ x ∈ deg U a n, pullHC f t ht x ∈ deg V a n) ∧
  ∀ {Z : Sch K} (g : Z ⟶ Y) (μ : Type) (W : μ → Z.left.Opens) (s : μ → κ) (hs : ∀ k, W k ≤ g.left ⁻¹ᵁ V (s k))
    (h : ∀ k, W k ≤ (g ≫ f).left ⁻¹ᵁ U ((t ∘ s) k)) (x : HC U n), pullHC g s hs (pullHC f t ht x) = pullHC (g ≫ f) (t ∘ s) h x

def PullInd : Prop := ∀ (K : Type) [CommRing K] {X Y : Sch K} (f : Y ⟶ X) (ι κ : Type) (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (t t' : κ → ι) (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j)) (ht' : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t' j)) (n : ℕ) (x : HC U n),
  pullHC f t ht x = pullHC f t' ht' x

def AugExact {W : TopCat.{0}} (Q : (Opens W)ᵒᵖ ⥤ AddCommGrpCat.{0}) {κ : Type} (V : κ → Opens W) (T : Opens W) {M : Type} [AddCommGroup M]
    (e : M →+ Q.obj (op T)) : Prop :=
  (∀ m : M, (∀ j, res Q (inf_le_right : V j ⊓ T ≤ T) (e m) = 0) → m = 0) ∧
  (∀ σ : Cochain Q (fun j => V j ⊓ T) 0, d Q _ 0 σ = 0 → ∃ m : M, ∀ i : Fin 1 → κ,
    σ i = res Q ((inter_le (fun j => V j ⊓ T) i 0).trans inf_le_right) (e m)) ∧ CechAcyclic Q fun j => V j ⊓ T

def Master : Prop := ∀ {W X : TopCat.{0}} (f : W ⟶ X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) (Q : (Opens W)ᵒᵖ ⥤ AddCommGrpCat.{0})
  (φ : P ⟶ (Opens.map f).op ⋙ Q) (ι κ : Type) (U : ι → Opens X) (V : κ → Opens W) (t : κ → ι)
  (c : ∀ n, Cochain P U n →+ Cochain Q V n),
  (∀ j, V j ≤ (Opens.map f).obj (U (t j))) →
  (∀ n σ (j : Fin (n + 1) → κ) (h : inter V j ≤ (Opens.map f).obj (inter U (t ∘ j))), c n σ j = res Q h (φ.app _ (σ (t ∘ j)))) →
  (∀ n (i : Fin (n + 1) → ι), AugExact Q V ((Opens.map f).obj (inter U i)) (φ.app (op (inter U i))).hom) →
  ∀ n, (∀ σ, d P U n σ = 0 → c n σ ∈ coboundaries Q V n → σ ∈ coboundaries P U n) ∧
    ∀ τ, d Q V n τ = 0 → ∃ σ, d P U n σ = 0 ∧ c n σ - τ ∈ coboundaries Q V n

def QC {X : Scheme.{0}} (P : (Opens X.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{0}) (S : X.Opens → Prop) : Prop :=
  ∀ T : X.Opens, IsAffineOpen T → S T → ∀ (κ : Type) [Finite κ] (h : κ → Γ(X, T)), (⨆ j, X.basicOpen (h j)) = T →
    AugExact P (fun j => X.basicOpen (h j)) T (AddMonoidHom.id _)

def QCAll : Prop := ∀ {X : Scheme.{0}} [X.IsSeparated] (P : (Opens X.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{0}) (S : X.Opens → Prop),
  (∀ T T', T' ≤ T → S T → S T') → QC P S → ∀ T : X.Opens, IsAffineOpen T → S T → ∀ (κ : Type) (V : κ → X.Opens),
    (∀ j, IsAffineOpen (V j)) → T ≤ iSup V → AugExact P V T (AddMonoidHom.id _)

def FmQC : Prop := ∀ (K : Type) [CommRing K] (X : Sch K), ∃ (P : (Opens X.left.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{0})
  (e : ∀ U : X.left.Opens, Fm K (Sec X U) ≃+ P.obj (op U)),
  (∀ (U V : X.left.Opens) (h : V ≤ U) x, e V (fmMap (secRes X h) x) = res P h (e U x)) ∧ QC P fun _ => True

def Ref : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) [X.left.IsSeparated] (ι : Type) (U : ι → X.left.Opens) (hU : IsCov U) (n : ℕ),
  Function.Bijective (down hU (n := n))

def PullLaws : Prop := ∀ (K : Type) [CommRing K] {X Y : Sch K} [Y.left.IsSeparated] (f : Y ⟶ X) (n : ℕ),
  IsLinearMap K (pull f (n := n)) ∧ (∀ (a b : ℕ) (h : a + b = n) (x : H X a) (y : H X b), pull f (cup h x y) = cup h (pull f x) (pull f y)) ∧
  pull f (one X) = one Y ∧
  (∀ (ι κ : Type) (U : ι → X.left.Opens) (V : κ → Y.left.Opens) (hU : IsCov U) (hV : IsCov V) (t : κ → ι)
    (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j)) (x : H X n), down hV (pull f x) = pullHC f t ht (down hU x)) ∧
  (∀ x : H Y n, pull (𝟙 Y) x = x) ∧ ∀ {Z : Sch K} [Z.left.IsSeparated] (g : Z ⟶ Y) (x : H X n), pull g (pull f x) = pull (g ≫ f) x

def DegLaws : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (ι : Type) (U : ι → X.left.Opens) (n : ℕ),
  iSupIndep (fun a => deg U a n) ∧ ∀ D : ℕ, (∀ (m : ℕ) (i : Fin (m + 1) → ι) (a : ℕ), D < a →
    ⋀[Sec X (cap U i)]^a Ω[Sec X (cap U i)⁄K] = ⊥) → (⨆ a ∈ Finset.range (D + 1), deg U a n) = ⊤ ∧ ∀ a, D < a → deg U a n = ⊥

def DegPull : Prop := ∀ (K : Type) [CommRing K] {X Y : Sch K} [Y.left.IsSeparated] (a n : ℕ),
  (∀ (κ : Type) (V : κ → Y.left.Opens) (hV : IsCov V) (y : H Y n), y ∈ Hd Y a n ↔ down hV y ∈ deg V a n) ∧
  ∀ f : Y ⟶ X, ∀ x ∈ Hd X a n, pull f x ∈ Hd Y a n

def SmoothTop : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (D : ℕ) [SmoothOfRelativeDimension D X.hom] (U : X.left.Opens),
  IsAffineOpen U → ∀ a, D < a → ⋀[Sec X U]^a Ω[Sec X U⁄K] = ⊥

def FirstChernClassLaws : Prop := ∀ (K : Type) [CommRing K] {X : Sch K} [X.left.IsSeparated] (L : Coc X),
  dC L.U 1 (fun i => dlog K (L.g i)) = 0 ∧ down L.cov (c1 L) = cls (fun i => dlog K (L.g i)) ∧ c1 L ∈ Hd X 1 1 ∧
  ∀ {Y : Sch K} [Y.left.IsSeparated] (f : Y ⟶ X) (M : Coc Y) (t : M.ι → L.ι) (ht : ∀ j, M.U j ≤ f.left ⁻¹ᵁ L.U (t j)),
    (∀ j, ((M.g j : (Sec Y (cap M.U j))ˣ) : Sec Y (cap M.U j)) = secMap f (cap_le f t ht j) (L.g (t ∘ j)).val) → pull f (c1 L) = c1 M

structure IsDiv {K : Type} [CommRing K] {W E : Sch K} (i : E ⟶ W) (L : Coc W) (s : ∀ j : L.ι, Sec W (L.U j)) : Prop where
  closed : IsClosedImmersion i.left
  ker : ∀ j, RingHom.ker (secMap i (le_refl (i.left ⁻¹ᵁ L.U j))).toRingHom = Ideal.span {s j}
  nzd : ∀ j, s j ∈ nonZeroDivisors (Sec W (L.U j))
  rel : ∀ j : Fin 2 → L.ι, secRes W (inter_le (X := W.left.toTopCat) L.U j 0) (s (j 0)) =
    (L.g j).val * secRes W (inter_le (X := W.left.toTopCat) L.U j 1) (s (j 1))

def H1 : Prop := ∀ (K : Type) [Field K] {W E : Sch K} [W.left.IsSeparated] [Smooth W.hom] (i : E ⟶ W) (L : Coc W)
  (s : ∀ j : L.ι, Sec W (L.U j)), IsDiv i L s → ∀ (n : ℕ) (z : H W n), pull i z = 0 → cup (add_comm 1 n) (c1 L) z = 0

end UpperTheory.Gal.DifferentialFormSections
end
end
