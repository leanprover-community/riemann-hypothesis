import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

def uIdeal (D : Datum p) (r : ℤ) : Ideal (𝓞 D.F) := Ideal.span {(p : 𝓞 D.F), D.ω - (r : 𝓞 D.F)}

theorem p_mem_uIdeal (D : Datum p) (r : ℤ) : (p : 𝓞 D.F) ∈ uIdeal D r :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem sub_mem_uIdeal (D : Datum p) (r : ℤ) : D.ω - (r : 𝓞 D.F) ∈ uIdeal D r :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))


def IsPIsog {N : ℕ} {s : S ⟶ Sp R} (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) : Prop :=
  (∃ k : ℕ, c = p ^ k) ∧
  IsMonHom ψ ∧ (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta x ≫ ψ) ∧
    Nonempty (LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ))) ∧
    ∃ ψ' : o'.A ⟶ o.A, IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 o.A) ^ c ∧ ψ' ≫ ψ = (𝟙 o'.A) ^ c

theorem IsPIsog.exists_eq_pow {N : ℕ} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) : ∃ k : ℕ, c = p ^ k := h.1

theorem IsPIsog.pos {N : ℕ} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) : 0 < c := by
  obtain ⟨k, rfl⟩ := h.1
  exact pow_pos (Fact.out : p.Prime).pos k

def KilledBy {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (v : Ideal (𝓞 D.F)) {T : Over S} (g : T ⟶ o.A) : Prop :=
  ∀ a ∈ v, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1

def IsTj {N : ℕ} {s : S ⟶ Sp R} (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S),
    (∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)

structure TjCorr {N : ℕ} (F : RepFam b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) where

  Y : Scheme.{0}

  s : Y ⟶ F.X

  t : Y ⟶ F.X
  st : s ≫ F.s = t ≫ F.s

  o : Obj b N (s ≫ F.s)

  o' : Obj b N (s ≫ F.s)
  ms : ObjMap o F.univ s
  mt : ObjMap o' F.univ t

  ψ : o.A ⟶ o'.A
  isog : IsPIsog c o o' ψ
  tj : IsTj r w j o o' ψ

  wPrime : w.IsPrime

  uLe : uIdeal D r ≤ w

  pReg : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0

  sFin : IsFinite s

  tFin : IsFinite t

  sSurj : Surjective s

theorem TjCorr.p_mem {N : ℕ} {F : RepFam b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (T : TjCorr F r w j c) :
    (p : 𝓞 D.F) ∈ w :=
  T.uLe (p_mem_uIdeal D r)





theorem IsPIsog.id {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) : IsPIsog 1 o o (𝟙 o.A) := by
  have e : sq2 (𝟙 o.A) = 𝟙 (G2 o.A).left := by
    simp only [sq2, Category.comp_id, lift_fst_snd]; rfl
  refine ⟨⟨0, (pow_zero p).symm⟩, inferInstance, fun c' => ?_, fun x => (Category.comp_id _).symm, ?_, 𝟙 o.A,
    inferInstance, ?_, ?_⟩
  · rw [Category.comp_id, Category.id_comp]
  · refine ⟨(GlobalTheory.PrimNorm.lbIso_iff o.isLB _ _ _ _).2 ?_⟩
    show _ = ∏ _k : PUnit, GlobalTheory.PrimNorm.cls o.P (sq2 (𝟙 o.A)) ^ (1 : ℤ)
    rw [e]
    simp
  · rw [pow_one, Category.comp_id]
  · rw [pow_one, Category.comp_id]

theorem KilledBy.one {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (v : Ideal (𝓞 D.F)) (T : Over S) :
    KilledBy o v (1 : T ⟶ o.A) := fun a _ => by
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
  exact one_comp _

theorem IsTj.id {N : ℕ} {s : S ⟶ Sp R} (r : ℤ) (w : Ideal (𝓞 D.F)) (o : Obj b N s) :
    IsTj r w 0 o o (𝟙 o.A) := by
  intro k _ _ _ x
  refine ⟨fun g hg _ => ?_, ?_⟩
  · rw [Category.comp_id] at hg
    subst hg
    exact KilledBy.one o w _
  · rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, by rw [Category.comp_id], KilledBy.one o w _⟩, fun y => Subtype.ext ?_⟩
    have := y.2.1
    rw [Category.comp_id] at this
    exact this


theorem pReg_of_flat {Y : Scheme.{0}} (s : Y ⟶ Sp R) [Flat s] (hR : ∀ a : R, (p : R) * a = 0 → a = 0)
    (U : Y.Opens) (f : Γ(Y, U)) (hf : (p : Γ(Y, U)) * f = 0) : f = 0 := by
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · have hfl : (s.appLE ⊤ V.1.1 le_top).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) s inferInstance ⟨⊤, isAffineOpen_top _⟩ V.1 le_top
    have hp : (p : Γ(Sp R, ⊤)) ∈ nonZeroDivisors Γ(Sp R, ⊤) := by
      rw [mem_nonZeroDivisors_iff_left]
      intro a ha
      let e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
      refine e.injective ((hR _ ?_).trans (map_zero e).symm)
      rw [← map_natCast e, ← map_mul, ha, map_zero]
    letI := (s.appLE ⊤ V.1.1 le_top).hom.toAlgebra
    haveI : Module.Flat Γ(Sp R, ⊤) Γ(Y, V.1.1) := hfl
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(Y, V.1.1)) hp
    let ρ : Γ(Y, U) →+* Γ(Y, V.1.1) := (Y.presheaf.map (homOfLE V.2).op).hom
    show ρ f = ρ 0
    refine hreg ?_
    simp only [Algebra.smul_def, map_natCast, map_zero, mul_zero]
    rw [← map_natCast ρ, ← map_mul, hf, map_zero]

theorem pReg_of_isUnit {Y : Scheme.{0}} (s : Y ⟶ Sp R) (hR : IsUnit (p : R))
    (U : Y.Opens) (f : Γ(Y, U)) (hf : (p : Γ(Y, U)) * f = 0) : f = 0 := by
  have := hR.map (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appLE ⊤ U le_top).hom)
  rw [map_natCast] at this
  exact this.mul_right_eq_zero.1 hf


def IsWOrd {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) {k : Type} [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) : Prop :=
  CharP k p ∧ w.IsPrime ∧ (p : 𝓞 D.F) ∈ w ∧
    Nat.card {g : Over.mk x ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * (D.n - 1))


example (w : Ideal (𝓞 D.F)) (j : ℕ) (h : D.m = 1) : Ideal.absNorm w ^ (D.m * j) = Ideal.absNorm w ^ j := by
  rw [h, Nat.one_mul]

example (w : Ideal (𝓞 D.F)) : Ideal.absNorm w ^ (D.m * 0) = 1 := by simp

example : ∃ k : ℕ, (1 : ℕ) = p ^ k := ⟨0, (pow_zero p).symm⟩

end GlobalTheory.UPel.HT.ES
