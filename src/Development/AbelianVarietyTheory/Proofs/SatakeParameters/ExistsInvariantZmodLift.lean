import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUMulInfU
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSpaceDefiniteUnitaryInfinitePoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory

theorem isOfFinOrder_of_conj_mem_ratU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Subgroup (UA E n)),
    IsCompact (D : Set (UA E n)) → ∀ (g : UA E n), ∀ c ∈ D, g * c * g⁻¹ ∈ ratU E n → IsOfFinOrder c := by
  intro E _ _ _ n D hD g c hc hgc
  haveI : DiscreteTopology (ratGL E n).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n
  have hcl : IsClosed (((ratGL E n).range : Subgroup (GA E n)) : Set (GA E n)) := Subgroup.isClosed_of_discrete
  let K : Set (GA E n) := (fun x : UA E n => ((g * x * g⁻¹ : UA E n) : GA E n)) '' (D : Set (UA E n))
  have hK : IsCompact K := hD.image (continuous_subtype_val.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hKG : IsCompact (K ∩ ((ratGL E n).range : Set (GA E n))) := hK.inter_right hcl
  let t : Set (ratGL E n).range := {x | (x : GA E n) ∈ K}
  have himg : Subtype.val '' t = K ∩ ((ratGL E n).range : Set (GA E n)) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
    · rintro ⟨hy, hy'⟩; exact ⟨⟨y, hy'⟩, hy, rfl⟩
  have ht : IsCompact t := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]; exact hKG
  have hfin : (K ∩ ((ratGL E n).range : Set (GA E n))).Finite := by
    rw [← himg]; exact (ht.finite_of_discrete).image _
  by_contra hno
  have hinj := (injective_pow_iff_not_isOfFinOrder).2 hno
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((g * c ^ k * g⁻¹ : UA E n) : GA E n)) ?_ ?_ hfin
  · intro i j hij
    apply hinj
    have h1 : g * c ^ i * g⁻¹ = g * c ^ j * g⁻¹ := Subtype.ext hij
    simpa using h1
  · intro k
    refine ⟨⟨c ^ k, D.pow_mem hc k, rfl⟩, ?_⟩
    have hk : g * c ^ k * g⁻¹ ∈ ratU E n := by
      have := (ratU E n).pow_mem hgc k
      simpa [conj_pow] using this
    exact (Subgroup.mem_subgroupOf).1 hk

end GlobalTheory
end
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Subgroup (UA E n)), IsCompact (D : Set (UA E n)) → ∀ (g : UA E n), ∀ c ∈ D, g * c * g⁻¹ ∈ ratU E n → IsOfFinOrder c := by
  first | exact @GlobalTheory.isOfFinOrder_of_conj_mem_ratU | exact GlobalTheory.isOfFinOrder_of_conj_mem_ratU | (intros; apply GlobalTheory.isOfFinOrder_of_conj_mem_ratU; all_goals assumption)
end

section
open GlobalTheory.Cong

namespace GlobalTheory

theorem exists_leftInv_rightEquivariant (G A : Type) [Group G] [AddCommGroup A] (Γ C : Subgroup G)
    (lam : C →* Multiplicative A)
    (h : ∀ g : G, ∀ γ ∈ Γ, ∀ c : C, γ * g = g * c → lam c = 1) :
    ∃ ℓ : G → A, (∀ γ ∈ Γ, ∀ g, ℓ (γ * g) = ℓ g) ∧
      ∀ g (c : C), ℓ (g * c) = ℓ g + Multiplicative.toAdd (lam c) := by

  have key : ∀ (s γ γ' : G), γ ∈ Γ → γ' ∈ Γ → ∀ c c' : C,
      γ * s * c = γ' * s * c' → lam c = lam c' := by
    intro s γ γ' hγ hγ' c c' e
    have e2 : (γ'⁻¹ * γ) * s = s * ((c' * c⁻¹ : C) : G) := by
      push_cast
      calc γ'⁻¹ * γ * s = γ'⁻¹ * (γ * s * c) * (c : G)⁻¹ := by group
        _ = γ'⁻¹ * (γ' * s * c') * (c : G)⁻¹ := by rw [e]
        _ = s * ((c' : G) * (c : G)⁻¹) := by group
    have := h s _ (Γ.mul_mem (Γ.inv_mem hγ') hγ) _ e2
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this.symm
  let S : Setoid G :=
    { r := fun a b => ∃ γ ∈ Γ, ∃ c : C, b = γ * a * c
      iseqv := by
        refine ⟨fun a => ⟨1, Γ.one_mem, 1, by simp⟩, ?_, ?_⟩
        · rintro a b ⟨γ, hγ, c, rfl⟩
          exact ⟨γ⁻¹, Γ.inv_mem hγ, c⁻¹, by push_cast; group⟩
        · rintro a b d ⟨γ, hγ, c, rfl⟩ ⟨γ', hγ', c', rfl⟩
          exact ⟨γ' * γ, Γ.mul_mem hγ' hγ, c * c', by push_cast; group⟩ }
  let rep : G → G := fun g => (Quotient.mk S g).out
  have hrep : ∀ g, ∃ c : C, ∃ γ ∈ Γ, g = γ * rep g * c := by
    intro g
    obtain ⟨γ, hγ, c, e⟩ := Quotient.mk_out (s := S) g
    exact ⟨c, γ, hγ, e⟩
  have rep_eq : ∀ a b, S.r a b → rep a = rep b := by
    intro a b hab
    simp only [rep]
    rw [Quotient.sound hab]
  let cf : G → C := fun g => Classical.choose (hrep g)
  have hcf : ∀ g, ∃ γ ∈ Γ, g = γ * rep g * cf g := fun g => Classical.choose_spec (hrep g)
  refine ⟨fun g => Multiplicative.toAdd (lam (cf g)), ?_, ?_⟩
  · intro γ hγ g
    simp only
    congr 1
    have hr : rep (γ * g) = rep g := (rep_eq _ _ ⟨γ, hγ, 1, by simp⟩).symm
    obtain ⟨γ1, hγ1, e1⟩ := hcf (γ * g)
    obtain ⟨γ2, hγ2, e2⟩ := hcf g
    rw [hr] at e1
    apply key (rep g) (γ⁻¹ * γ1) γ2 (Γ.mul_mem (Γ.inv_mem hγ) hγ1) hγ2
    calc γ⁻¹ * γ1 * rep g * (cf (γ * g) : G) = γ⁻¹ * (γ1 * rep g * cf (γ * g)) := by group
      _ = g := by rw [← e1]; group
      _ = γ2 * rep g * cf g := e2
  · intro g c
    simp only
    rw [← toAdd_mul]
    congr 1
    have hr : rep (g * c) = rep g := (rep_eq _ _ ⟨1, Γ.one_mem, c, by simp⟩).symm
    obtain ⟨γ1, hγ1, e1⟩ := hcf (g * c)
    obtain ⟨γ2, hγ2, e2⟩ := hcf g
    rw [hr] at e1
    have := key (rep g) γ1 γ2 hγ1 hγ2 (cf (g * c) * c⁻¹) (cf g) (by
      push_cast
      calc γ1 * rep g * ((cf (g * c) : G) * (c : G)⁻¹) = (γ1 * rep g * cf (g * c)) * (c : G)⁻¹ := by group
        _ = g := by rw [← e1]; group
        _ = γ2 * rep g * cf g := e2)
    rw [map_mul, map_inv] at this
    rw [← this]; group

example : ∀ (G A : Type) [Group G] [AddCommGroup A] (Γ C : Subgroup G) (lam : C →* Multiplicative A), (∀ g : G, ∀ γ ∈ Γ, ∀ c : C, γ * g = g * c → lam c = 1) → ∃ ℓ : G → A, (∀ γ ∈ Γ, ∀ g, ℓ (γ * g) = ℓ g) ∧ ∀ g (c : C), ℓ (g * c) = ℓ g + Multiplicative.toAdd (lam c) := exists_leftInv_rightEquivariant

end GlobalTheory
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

open Matrix

namespace GlobalTheory.EllU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* UA E n where
  toFun g := ⟨finGL E n (GeneralLinearGroup.map (pFin E) g.1),
    GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin g)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem finPart_mem (g : UA E n) : finPart g ∈ finU E n := pInf_finGL _

theorem finPart_of_finU {k : UA E n} (hk : k ∈ finU E n) : finPart k = k :=
  Subtype.ext (GlobalTheory.DefU.ClassFin.finGL_pFin ⟨k, hk⟩)

theorem finPart_of_infU {x : UA E n} (hx : x ∈ infU E n) : finPart x = 1 := by
  have h : GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  refine Subtype.ext ?_
  change finGL E n (GeneralLinearGroup.map (pFin E) x.1) = 1
  rw [h, map_one]

theorem inv_finPart_mul_mem (g : UA E n) : (finPart g)⁻¹ * g ∈ infU E n := by
  change GeneralLinearGroup.map (pFin E) ((finPart g)⁻¹ * g).1 = 1
  have h : GeneralLinearGroup.map (pFin E) (finPart g).1 = GeneralLinearGroup.map (pFin E) g.1 := pFin_finGL _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, inv_mul_cancel]

theorem continuous_finPart : Continuous (finPart (E := E) (n := n)) := by
  have h1 : Continuous (GeneralLinearGroup.map (pFin E) : GA E n → GL (Fin n) (Af E)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
  exact Continuous.subtype_mk (GlobalTheory.DefU.ClassFin.continuous_finGL.comp (h1.comp continuous_subtype_val)) _

end GlobalTheory.EllU
end
end
