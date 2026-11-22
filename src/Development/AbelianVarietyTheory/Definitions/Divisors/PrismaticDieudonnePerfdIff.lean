module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.PerfdLat

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

attribute [instance] PrismData.projective PrismData.finite

section Const

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

section BaseChange

variable (O' : Type) [CommRing O'] [Algebra O O'] {G : PDivGroup p O}

theorem baseChange_mulP (G : PDivGroup p O) (n : ℕ) : (G.baseChange O').mulP n = PDiv.bcMap O' (G.mulP n) :=
  PDiv.bc_hom_ext fun a => by
    obtain ⟨b, rfl⟩ := G.res_surjective n a
    have h := map_nsmul (AddMonoidHom.mk' (baseChangeMap (G := G) (H := G) O') (baseChangeMap_add O')) p (𝟙 G)
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul ℤ_[p]] at h
    have h1 : baseChangeMap O' ((p : ℤ_[p]) • 𝟙 G) = (p : ℤ_[p]) • 𝟙 (G.baseChange O') :=
      h.trans (congrArg _ ((baseChangeFunctor p O O').map_id G))
    have h2 := congrArg (fun f => Hom.app f (n + 1) (1 ⊗ₜ b)) h1
    simp only [baseChangeMap_app, natCast_smul_id_app] at h2
    rw [PDiv.bcMap_tmul, mulP_res]
    exact ((G.baseChange O').mulP_res n (1 ⊗ₜ b)).trans h2.symm

@[simp] theorem bcTate_pt (t : G.Tate) (n : ℕ) (r : O') (a : G.A n) :
    (bcTate O' t).pt n (r ⊗ₜ a) = r * algebraMap O O' (t.pt n a) := rfl

@[simp] theorem charElem_bcChar (χ : G.dual.Tate) (n : ℕ) : charElem (bcChar O' χ) n = 1 ⊗ₜ charElem χ n :=
  CartierDual.eq_of_forall_apply (R := O') fun φ => apply_charElem _ n φ

def dualBaseChange (G : PDivGroup p O) : (G.baseChange O').dual ≅ G.dual.baseChange O' where
  hom := ⟨fun n => CartierDual.baseChangeHom O O' (G.A n), fun n => BialgHom.ext fun x => by
    change CartierDual.map ((G.baseChange O').mulP n) _ = _
    rw [baseChange_mulP]
    exact (CartierDual.baseChange_map O' (G.mulP n) x).symm⟩
  inv := ⟨fun n => (CartierDual.baseChange O O' (G.A n)).symm, fun n => BialgHom.ext fun x => by
    obtain ⟨y, rfl⟩ := (CartierDual.baseChange O O' (G.A (n + 1))).surjective x
    change PDiv.bcMap O' (CartierDual.map (G.mulP n)) ((CartierDual.baseChange O O' (G.A (n + 1))).symm
      (CartierDual.baseChange O O' (G.A (n + 1)) y)) = (CartierDual.baseChange O O' (G.A n)).symm
        (CartierDual.map ((G.baseChange O').mulP n) (CartierDual.baseChange O O' (G.A (n + 1)) y))
    rw [baseChange_mulP, PDiv.bcMap, PDiv.bcMap, ← CartierDual.baseChange_map, BialgEquiv.symm_apply_apply,
      BialgEquiv.symm_apply_apply]⟩
  hom_inv_id := PDivGroup.Hom.ext <| funext fun n => BialgHom.ext fun a =>
    (CartierDual.baseChange O O' (G.A n)).apply_symm_apply a
  inv_hom_id := PDivGroup.Hom.ext <| funext fun n => BialgHom.ext fun a =>
    (CartierDual.baseChange O O' (G.A n)).symm_apply_apply a

end BaseChange

namespace ConstTate

variable {ε : (PDivGroup.mu p O).Tate} {G : PDivGroup p O}

variable (c : ConstTate ε G)

section BaseChange

variable (O' : Type) [CommRing O'] [Algebra O O']

end BaseChange

end ConstTate

end Const

section Lattices

open scoped Pointwise

section Quot

variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

end Quot

variable {p : ℕ} [Fact p.Prime]

section Ring

variable (S : CycPerfd p)

instance thetaSurjective : RingHomSurjective (fontaineTheta S.R p) := ⟨S.surj⟩

def eps : (PDivGroup.mu p S.R).Tate := muTate S.R (zeta S.ε) S.zeta_zero (zeta_succ_pow S.ε)

@[simp] theorem muRoot_eps (n : ℕ) : muRoot (eps S) n = zeta S.ε n := muRoot_muTate ..

end Ring

variable (D : PrismData p) {S : CycPerfd p}

@[simp] theorem PrismData.eCoord_smul_e (a : Ainf p S.R) : D.eCoord S (a • D.e S) = a :=
  (LinearEquiv.ofBijective _ (D.e_bijective S)).symm_apply_apply a

variable {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

end Lattices

end GlobalTheory.PerfdLat
