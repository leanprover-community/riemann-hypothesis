module

public import Mathlib

@[expose] public section

noncomputable section

open NumberField Matrix IsDedekindDomain
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.LKTrip

section Sim

variable {S A : Type*} [CommRing S] [CommRing A] {n : ℕ}

variable {S' A' : Type*} [CommRing S'] [CommRing A']

end Sim

section Points

variable (F : Type) [Field F] [NumberField F] [IsCMField F] {n : ℕ} (H : Matrix (Fin n) (Fin n) F)

def conjQ : F →ₐ[ℚ] F := RingHom.toRatAlgHom ((IsCMField.complexConj F).toRingEquiv.toRingHom)

@[simp] theorem conjQ_apply (x : F) : conjQ F x = IsCMField.complexConj F x := rfl

def conjT (R : Type) [CommRing R] [Algebra ℚ R] : R ⊗[ℚ] F →+* R ⊗[ℚ] F :=
  (Algebra.TensorProduct.map (AlgHom.id ℚ R) (conjQ F)).toRingHom

@[simp] theorem conjT_tmul (R : Type) [CommRing R] [Algebra ℚ R] (r : R) (x : F) :
    conjT F R (r ⊗ₜ x) = r ⊗ₜ IsCMField.complexConj F x := rfl

variable {F H}

end Points

section Topology

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ} {H : Matrix (Fin n) (Fin n) F}

end Topology

section Adeles

def AwayP (p : ℕ) : Type := {v : HeightOneSpectrum ℤ // v.asIdeal ≠ Ideal.span {(p : ℤ)}}

variable (p : ℕ)

def AfP : Type := Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]

instance : CommRing (AfP p) := inferInstanceAs <|
  CommRing <| Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]

instance : TopologicalSpace (AfP p) := inferInstanceAs <|
  TopologicalSpace <| Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]

instance : IsTopologicalRing (AfP p) :=
  haveI : Fact (∀ v : AwayP p,
      IsOpen (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  RestrictedProduct.isTopologicalRing (fun (v : AwayP p) ↦ v.1.adicCompletion ℚ)

def AfP.restr : FiniteAdeleRing ℤ ℚ →+* AfP p :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ) Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ ↦ RingHom.id _) (Filter.Eventually.of_forall fun _ ↦ Set.mapsTo_id _)

def AfP.diag : ℚ →+* AfP p := (AfP.restr p).comp (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))

instance : Algebra ℚ (AfP p) := (AfP.diag p).toAlgebra

def AfP.eval {p : ℕ} (v : AwayP p) : AfP p →ₐ[ℚ] v.1.adicCompletion ℚ :=
  { RestrictedProduct.evalRingHom (fun v : AwayP p ↦ v.1.adicCompletion ℚ) v with
    commutes' := fun k ↦ DFunLike.congr_fun (RingHom.ext_rat
      ((RestrictedProduct.evalRingHom (fun v : AwayP p ↦ v.1.adicCompletion ℚ) v).comp (algebraMap ℚ (AfP p)))
      (algebraMap ℚ (v.1.adicCompletion ℚ))) k }

end Adeles

section Signature

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ} {H : Matrix (Fin n) (Fin n) F}

def gramAt (H : Matrix (Fin n) (Fin n) F) (τ : F →+* ℂ) : Matrix (Fin n) (Fin n) ℂ := (H.map τ)ᵀ

theorem isHermitian_gramAt (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (τ : F →+* ℂ) :
    (gramAt H τ).IsHermitian := by
  have hH' : H.map (IsCMField.complexConj F : F →+* F) = Hᵀ := by
    rw [← Matrix.transpose_transpose (H.map _), hH]
  unfold Matrix.IsHermitian gramAt
  rw [Matrix.conjTranspose, Matrix.transpose_transpose]
  ext i j
  have := congrArg (fun M => τ (M i j)) hH'
  simp only [Matrix.map_apply, Matrix.transpose_apply] at this ⊢
  rw [← this]
  have h2 : τ ((IsCMField.complexConj F : F →+* F) (H i j)) = (starRingEnd ℂ) (τ (H i j)) :=
    IsCMField.complexEmbedding_complexConj F τ (H i j)
  rw [h2]; rfl

def sigPos (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (τ : F →+* ℂ) : ℕ :=
  Fintype.card {i : Fin n // 0 < (isHermitian_gramAt hH τ).eigenvalues i}

def sigNeg (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (τ : F →+* ℂ) : ℕ :=
  Fintype.card {i : Fin n // (isHermitian_gramAt hH τ).eigenvalues i < 0}

end Signature

section Sign

def sigPosH {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : Fin n // 0 < hA.eigenvalues i}

def sigNegH {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : Fin n // hA.eigenvalues i < 0}

end Sign

section UGroup

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

def uGroup (σ : S →+* Sᵐᵒᵖ) : Subgroup (Sˣ × Aˣ) where
  carrier := {x | ((x.1 : Sˣ) : S) * (σ ((x.1 : Sˣ) : S)).unop = algebraMap A S ((x.2 : Aˣ) : A)}
  mul_mem' := by
    rintro ⟨g, c⟩ ⟨h, d⟩ hg hh
    change (g : S) * (σ g).unop = algebraMap A S c at hg
    change (h : S) * (σ h).unop = algebraMap A S d at hh
    change ((g * h : Sˣ) : S) * (σ ((g * h : Sˣ) : S)).unop = algebraMap A S ((c * d : Aˣ) : A)
    rw [Units.val_mul, Units.val_mul, map_mul, MulOpposite.unop_mul, map_mul]
    calc (g : S) * h * ((σ h).unop * (σ g).unop) = g * (h * (σ h).unop) * (σ g).unop := by
          simp only [mul_assoc]
      _ = algebraMap A S d * ((g : S) * (σ g).unop) := by
          rw [hh, ← Algebra.commutes, mul_assoc]
      _ = algebraMap A S c * algebraMap A S d := by rw [hg]; exact Algebra.commutes _ _
  one_mem' := by
    change ((1 : Sˣ) : S) * (σ ((1 : Sˣ) : S)).unop = algebraMap A S ((1 : Aˣ) : A)
    simp
  inv_mem' := by
    rintro ⟨g, c⟩ hg
    change (g : S) * (σ g).unop = algebraMap A S c at hg
    change ((g⁻¹ : Sˣ) : S) * (σ ((g⁻¹ : Sˣ) : S)).unop = algebraMap A S ((c⁻¹ : Aˣ) : A)
    have hst : (σ g).unop * (σ ((g⁻¹ : Sˣ) : S)).unop = 1 := by
      rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
    have hcc : algebraMap A S ((c⁻¹ : Aˣ) : A) * algebraMap A S (c : A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have key : algebraMap A S (c : A) * (((g⁻¹ : Sˣ) : S) * (σ ((g⁻¹ : Sˣ) : S)).unop) = 1 := by
      rw [← mul_assoc, Algebra.commutes, ← hg, ← mul_assoc, Units.inv_mul, one_mul, hst]
    calc _ = algebraMap A S ((c⁻¹ : Aˣ) : A) *
          (algebraMap A S (c : A) * (((g⁻¹ : Sˣ) : S) * (σ ((g⁻¹ : Sˣ) : S)).unop)) := by
          rw [← mul_assoc, hcc, one_mul]
      _ = _ := by rw [key, mul_one]

theorem mem_uGroup {σ : S →+* Sᵐᵒᵖ} {x : Sˣ × Aˣ} :
    x ∈ uGroup σ ↔ ((x.1 : Sˣ) : S) * (σ ((x.1 : Sˣ) : S)).unop = algebraMap A S ((x.2 : Aˣ) : A) := Iff.rfl

variable {S' A' : Type*} [Ring S'] [CommRing A'] [Algebra A' S']

def uMap {σ : S →+* Sᵐᵒᵖ} {σ' : S' →+* S'ᵐᵒᵖ} (φ : S →+* S') (ψ : A →+* A')
    (hσ : ∀ x, (σ' (φ x)).unop = φ (σ x).unop) (hj : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (ψ a)) :
    uGroup (A := A) σ →* uGroup (A := A') σ' :=
  ((MonoidHom.prodMap (Units.map (φ : S →* S')) (Units.map (ψ : A →* A'))).comp
    (uGroup (A := A) σ).subtype).codRestrict _ fun x => by
    obtain ⟨⟨g, c⟩, hx⟩ := x
    have hx' : (g : S) * (σ g).unop = algebraMap A S c := hx
    show φ g * (σ' (φ g)).unop = algebraMap A' S' (ψ c)
    rw [hσ, ← map_mul, hx', hj]

end UGroup

section UPoints

variable {C : Type} [Ring C] [Algebra ℚ C] (star : C →+* Cᵐᵒᵖ)

def starT (R : Type) [CommRing R] [Algebra ℚ R] : R ⊗[ℚ] C →+* (R ⊗[ℚ] C)ᵐᵒᵖ :=
  (Algebra.TensorProduct.lift (Algebra.ofId R (R ⊗[ℚ] C)ᵐᵒᵖ)
    ((RingHom.op ((Algebra.TensorProduct.includeRight : C →ₐ[ℚ] R ⊗[ℚ] C) : C →+* R ⊗[ℚ] C)).comp
      star).toRatAlgHom
    (fun x _ => Algebra.commute_algebraMap_left x _)).toRingHom

theorem starT_tmul (R : Type) [CommRing R] [Algebra ℚ R] (r : R) (x : C) :
    (starT star R (r ⊗ₜ x)).unop = r ⊗ₜ (star x).unop := by
  change MulOpposite.unop (MulOpposite.op (r ⊗ₜ[ℚ] (1 : C)) * MulOpposite.op ((1 : R) ⊗ₜ[ℚ] (star x).unop)) = _
  rw [← MulOpposite.op_mul, MulOpposite.unop_op, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

def UPts (R : Type) [CommRing R] [Algebra ℚ R] : Subgroup ((R ⊗[ℚ] C)ˣ × Rˣ) :=
  uGroup (A := R) (starT star R)

variable {star}

def ubcMap {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R') :
    UPts star R →* UPts star R' :=
  uMap ((Algebra.TensorProduct.map f (AlgHom.id ℚ C)).toRingHom) (f : R →+* R')
    (fun x => by
      induction x using TensorProduct.inductionOn with
      | tmul r y =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          starT_tmul]
      | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy])
    (fun a => by simp [Algebra.TensorProduct.algebraMap_apply])

def uSimR (R : Type) [CommRing R] [Algebra ℚ R] : UPts star R →* Rˣ :=
  (MonoidHom.snd _ _).comp (UPts star R).subtype

variable [Module.Finite ℚ C]

instance UPts.instTop (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] :
    TopologicalSpace (UPts star R) :=
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  inferInstance

instance UPts.instTopGrp (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalGroup (UPts star R) :=
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[ℚ] C) := IsModuleTopology.isTopologicalRing R (R ⊗[ℚ] C)
  inferInstance

end UPoints

def LiesOver {p : ℕ} [Fact p.Prime] {F : Type} [Field F] (Kq : Subfield F) (u : Kq →+* ℚ_[p])
    (τ : F →+* PadicAlgCl p) : Prop :=
  ∀ x : Kq, τ x = algebraMap ℚ_[p] (PadicAlgCl p) (u x)

section Local

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

def FwOf (τ : F →+* PadicAlgCl p) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] (Set.range τ)

def embOf (τ : F →+* PadicAlgCl p) : F →+* FwOf τ :=
  τ.codRestrict (FwOf τ) (fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)

@[simp] theorem embOf_apply (τ : F →+* PadicAlgCl p) (x : F) : ((embOf τ x : FwOf τ) : PadicAlgCl p) = τ x := rfl

end Local

structure HTGroup (p : ℕ) [Fact p.Prime] where

  F : Type
  [fieldF : Field F]
  [numF : NumberField F]
  [cmF : IsCMField F]

  Kq : Subfield F
  hKq : Module.finrank ℚ Kq = 2 ∧ ∀ τ : F →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0

  u : Kq →+* ℚ_[p]

  n : ℕ
  n_pos : 0 < n

  C : Type
  [ringC : Ring C]
  [algC : Algebra F C]
  [algQC : Algebra ℚ C]
  [towerC : IsScalarTower ℚ F C]
  [finC : FiniteDimensional F C]
  [centralC : Algebra.IsCentral F C]
  [simpleC : IsSimpleRing C]
  rankC : Module.finrank F C = n ^ 2

  star : C →+* Cᵐᵒᵖ
  star_star : ∀ x, (star (star x).unop).unop = x

  star_F : ∀ x : F, (star (algebraMap F C x)).unop = algebraMap F C (IsCMField.complexConj F x)

  psi : InfinitePlace F → (C →+* Matrix (Fin n) (Fin n) ℂ)
  psi_F : ∀ v (x : F), psi v (algebraMap F C x) = Matrix.scalar (Fin n) (v.embedding x)

  gram : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ
  gram_herm : ∀ v, (gram v).IsHermitian
  gram_det : ∀ v, (gram v).det ≠ 0
  psi_star : ∀ v x, psi v (star x).unop = (gram v)⁻¹ * (psi v x)ᴴ * gram v

  sig : ∀ v, (sigPosH (gram_herm v) = 1 ∧ sigNegH (gram_herm v) = n - 1) ∨
    (sigPosH (gram_herm v) = 0 ∧ sigNegH (gram_herm v) = n)

  m : ℕ

  emb : Fin m → (F →+* PadicAlgCl p)
  emb_over : ∀ i, LiesOver Kq u (emb i)
  emb_inj : ∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
    ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i) = emb j → i = j
  emb_all : ∀ τ : F →+* PadicAlgCl p, LiesOver Kq u τ →
    ∃ i, ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      τ = ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i)

  rho : ∀ i : Fin m, C →+* Matrix (Fin n) (Fin n) (FwOf (emb i))
  rho_F : ∀ i (x : F), rho i (algebraMap F C x) = Matrix.scalar (Fin n) (embOf (emb i) x)

  iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p

  iotaC : AlgebraicClosure ℚ →+* ℂ

attribute [instance] HTGroup.fieldF HTGroup.numF HTGroup.cmF HTGroup.ringC HTGroup.algC HTGroup.algQC
  HTGroup.towerC HTGroup.finC HTGroup.centralC HTGroup.simpleC
section BcLemmas

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ} {H : Matrix (Fin n) (Fin n) F}

end BcLemmas
namespace HTGroup

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

instance finQ : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C

abbrev GAf : Type := UPts G.star (AfP p)

abbrev GQp : Type := UPts G.star ℚ_[p]

def a : ℕ := Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1}

abbrev Fw (i : Fin G.m) : IntermediateField ℚ_[p] (PadicAlgCl p) := FwOf (G.emb i)

def embW (i : Fin G.m) : G.F →+* G.Fw i := embOf (G.emb i)

def liftW (i : Fin G.m) : ℚ_[p] ⊗[ℚ] G.F →ₐ[ℚ] G.Fw i :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom ℚ ℚ_[p] (G.Fw i)) (G.embW i).toRatAlgHom
    (fun _ _ => Commute.all _ _)

def locW (i : Fin G.m) : ℚ_[p] ⊗[ℚ] G.C →ₐ[ℚ_[p]] Matrix (Fin G.n) (Fin G.n) (G.Fw i) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[p] _) (G.rho i).toRatAlgHom (fun x _ => Algebra.commute_algebraMap_left x _)

def localization₂ : G.GQp →* ℚ_[p]ˣ × ((i : Fin G.m) → GL (Fin G.n) (G.Fw i)) :=
  MonoidHom.prod (uSimR ℚ_[p]) (Pi.monoidHom fun i =>
    (Units.map ((G.locW i : ℚ_[p] ⊗[ℚ] G.C →+* Matrix (Fin G.n) (Fin G.n) (G.Fw i)) :
        ℚ_[p] ⊗[ℚ] G.C →* Matrix (Fin G.n) (Fin G.n) (G.Fw i))).comp
      ((MonoidHom.fst _ _).comp (UPts G.star ℚ_[p]).subtype))

def psiR (v : InfinitePlace G.F) : ℝ ⊗[ℚ] G.C →ₐ[ℝ] Matrix (Fin G.n) (Fin G.n) ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ _) (G.psi v).toRatAlgHom (fun x _ => Algebra.commute_algebraMap_left x _)

structure Level (G : HTGroup p) where

  K : OpenSubgroup G.GAf
  compact : IsCompact (K : Set G.GAf)

end HTGroup

namespace HTGroup

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

instance finiteDimensional_Fw (i : Fin G.m) : FiniteDimensional ℚ_[p] (G.Fw i) := by
  let b := Module.finBasis ℚ G.F
  have hle : G.Fw i ≤ IntermediateField.adjoin ℚ_[p] (Set.range (fun k => G.emb i (b k))) := by
    rw [Fw, FwOf, IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine sum_mem fun k _ => ?_
    have : G.emb i (b.repr x k • b k) = algebraMap ℚ_[p] (PadicAlgCl p) ((b.repr x k : ℚ) : ℚ_[p]) * G.emb i (b k) := by
      rw [Rat.smul_def, map_mul, map_ratCast, map_ratCast]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨k, rfl⟩)
  have hfin : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (Set.range (fun k => G.emb i (b k)))) := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro _ ⟨k, rfl⟩
    have h1 : IsIntegral ℚ (G.emb i (b k)) :=
      (Algebra.IsIntegral.isIntegral (R := ℚ) (b k)).map (G.emb i).toRatAlgHom
    exact h1.tower_top
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

end HTGroup

section Herm

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}

theorem map_nonsingInv {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) {A : Matrix (Fin n) (Fin n) K}
    (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero f) (map_one f)]

def hermStar (H : Matrix (Fin n) (Fin n) F) (hdet : H.det ≠ 0) :
    Matrix (Fin n) (Fin n) F →+* (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ where
  toFun x := MulOpposite.op ((H.map (IsCMField.complexConj F : F →+* F))⁻¹ *
    (x.map (IsCMField.complexConj F : F →+* F))ᵀ * H.map (IsCMField.complexConj F : F →+* F))
  map_one' := by
    have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero _).2 hdet |>.isUnit
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hu, MulOpposite.op_one]
  map_mul' x y := by
    have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero _).2 hdet |>.isUnit
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  map_zero' := by simp
  map_add' x y := by
    apply MulOpposite.unop_injective
    simp [Matrix.map_add (f := _), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem hermStar_apply (H : Matrix (Fin n) (Fin n) F) (hdet : H.det ≠ 0) (x : Matrix (Fin n) (Fin n) F) :
    (hermStar H hdet x).unop = (H.map (IsCMField.complexConj F : F →+* F))⁻¹ *
      (x.map (IsCMField.complexConj F : F →+* F))ᵀ * H.map (IsCMField.complexConj F : F →+* F) := rfl

theorem map_conj_conj (x : Matrix (Fin n) (Fin n) F) :
    (x.map (IsCMField.complexConj F : F →+* F)).map (IsCMField.complexConj F : F →+* F) = x := by
  ext i j
  simp [IsCMField.complexConj_apply_apply]

theorem hermStar_hermStar {H : Matrix (Fin n) (Fin n) F} (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H)
    (hdet : H.det ≠ 0) (x : Matrix (Fin n) (Fin n) F) :
    (hermStar H hdet (hermStar H hdet x).unop).unop = x := by
  have hT : H.map (IsCMField.complexConj F : F →+* F) = Hᵀ := by
    rw [← Matrix.transpose_transpose (H.map _), hH]
  have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hdet |>.isUnit
  have huH : IsUnit H.det := (Ne.isUnit hdet)
  rw [hermStar_apply, hermStar_apply, Matrix.map_mul, Matrix.map_mul, map_nonsingInv _ hu, map_conj_conj,
    Matrix.transpose_map, map_conj_conj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, ← hT]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul _ hu,
    Matrix.mul_one]

theorem hermStar_algebraMap (H : Matrix (Fin n) (Fin n) F) (hdet : H.det ≠ 0) (a : F) :
    (hermStar H hdet (algebraMap F (Matrix (Fin n) (Fin n) F) a)).unop =
      algebraMap F (Matrix (Fin n) (Fin n) F) (IsCMField.complexConj F a) := by
  have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hdet |>.isUnit
  have e : ((algebraMap F (Matrix (Fin n) (Fin n) F) a).map (IsCMField.complexConj F : F →+* F))ᵀ =
      algebraMap F (Matrix (Fin n) (Fin n) F) (IsCMField.complexConj F a) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.algebraMap_matrix_apply]
    · simp [Matrix.algebraMap_matrix_apply, h, Ne.symm h]
  rw [hermStar_apply, e, ← Algebra.commutes, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem map_algebraMap_eq_scalar {K L : Type*} [Field K] [CommRing L] (f : K →+* L) (a : K) :
    (algebraMap K (Matrix (Fin n) (Fin n) K) a).map f = Matrix.scalar (Fin n) (f a) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, h]

theorem mul_eq_smul_one_comm {K : Type*} [Field K] {A B : Matrix (Fin n) (Fin n) K} {c : K} (hc : c ≠ 0) :
    A * B = c • 1 ↔ B * A = c • 1 := by
  have key : ∀ A B : Matrix (Fin n) (Fin n) K, A * B = c • 1 → B * A = c • 1 := by
    intro A B h
    have h1 : A * (c⁻¹ • B) = 1 := by rw [Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have h2 := mul_eq_one_comm.1 h1
    rw [Matrix.smul_mul] at h2
    calc B * A = c • (c⁻¹ • (B * A)) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      _ = c • 1 := by rw [h2]
  exact ⟨key A B, key B A⟩

end Herm

def ofHerm {p : ℕ} [Fact p.Prime] (F : Type) [Field F] [NumberField F] [IsCMField F] (Kq : Subfield F)
    (hKq : Module.finrank ℚ Kq = 2 ∧ ∀ τ : F →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0) (u : Kq →+* ℚ_[p])
    (n : ℕ) (n_pos : 0 < n) (H : Matrix (Fin n) (Fin n) F)
    (herm : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (det_ne : H.det ≠ 0)
    (sig : ∀ τ : F →+* ℂ, (sigPos herm τ = 1 ∧ sigNeg herm τ = n - 1) ∨ (sigPos herm τ = 0 ∧ sigNeg herm τ = n))
    (m : ℕ) (emb : Fin m → (F →+* PadicAlgCl p)) (emb_over : ∀ i, LiesOver Kq u (emb i))
    (emb_inj : ∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i) = emb j → i = j)
    (emb_all : ∀ τ : F →+* PadicAlgCl p, LiesOver Kq u τ →
      ∃ i, ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        τ = ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i))
    (iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p) (iotaC : AlgebraicClosure ℚ →+* ℂ) : HTGroup p :=
  haveI : NeZero n := ⟨n_pos.ne'⟩
  { F := F
    Kq := Kq
    hKq := hKq
    u := u
    n := n
    n_pos := n_pos
    C := Matrix (Fin n) (Fin n) F
    rankC := by rw [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]; ring
    star := hermStar H det_ne
    star_star := hermStar_hermStar herm det_ne
    star_F := hermStar_algebraMap H det_ne
    psi := fun v => (v.embedding).mapMatrix
    psi_F := fun v x => map_algebraMap_eq_scalar _ x
    gram := fun v => gramAt H v.embedding
    gram_herm := fun v => isHermitian_gramAt herm v.embedding
    gram_det := fun v => by
      rw [gramAt, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero _).2 det_ne
    psi_star := fun v x => by
      have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact (map_ne_zero _).2 det_ne |>.isUnit
      have hT : H.map (IsCMField.complexConj F : F →+* F) = Hᵀ := by
        rw [← Matrix.transpose_transpose (H.map _), herm]
      have hg : (H.map (IsCMField.complexConj F : F →+* F)).map v.embedding = gramAt H v.embedding := by
        rw [hT, gramAt, Matrix.transpose_map]
      have hx : ((x.map (IsCMField.complexConj F : F →+* F))ᵀ).map v.embedding = (x.map v.embedding)ᴴ := by
        ext i j
        simp [Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj]
      show (_ : Matrix (Fin n) (Fin n) F).map v.embedding = _
      rw [hermStar_apply, Matrix.map_mul, Matrix.map_mul, map_nonsingInv _ hu, hg, hx]
      rfl
    sig := fun v => sig v.embedding
    m := m
    emb := emb
    emb_over := emb_over
    emb_inj := emb_inj
    emb_all := emb_all
    rho := fun i => (embOf (emb i)).mapMatrix
    rho_F := fun i x => map_algebraMap_eq_scalar _ x
    iotaP := iotaP
    iotaC := iotaC }

namespace Example

instance isCyclotomicExtension_QI : IsCyclotomicExtension {4} ℚ QI := CyclotomicField.isCyclotomicExtension 4 ℚ

instance isCMField_QI : IsCMField QI := IsCyclotomicExtension.Rat.isCMField (S := {4}) QI ⟨4, rfl, by norm_num⟩

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

end Example

namespace Example

end Example

end GlobalTheory.LKTrip
