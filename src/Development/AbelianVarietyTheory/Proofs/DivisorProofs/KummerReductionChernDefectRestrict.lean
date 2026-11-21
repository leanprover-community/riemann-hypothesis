import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistAltI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem res_defect : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ),
    IsUnit (Q : Γ(U, ⊤)) → Sec.res g (GlobalTheory.EtC.RedChern.defect Q q U v) =
      GlobalTheory.EtC.RedChern.defect Q q V (Units.map g.appTop.hom.toMonoidHom v) := by
  intro Q q _ hqQ V U g v hQ
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (zero_dvd_iff.mp hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hqU : IsUnit (q : Γ(U, ⊤)) := by
    obtain ⟨k, hk⟩ := hqQ
    rw [hk, Nat.cast_mul] at hQ
    exact isUnit_of_mul_isUnit_left hQ
  unfold defect
  rw [Sec.res, map_sub]
  change Sec.res g _ - Sec.res g _ = _
  rw [(redMap Q q 1).nat g 0, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting Q).1 V U g v hQ, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g _ hqU, map_pow]

end GlobalTheory.EtC.RedChern
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_restriction : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → Sec.res g (GlobalTheory.EtC.RedChern.defect Q q U v) = GlobalTheory.EtC.RedChern.defect Q q V (Units.map g.appTop.hom.toMonoidHom v) := by
  atlas_forward_decl GlobalTheory.EtC.RedChern.res_defect
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defect_mul_prim (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (v w : (Γ(U, ⊤))ˣ) (h : (w : Γ(U, ⊤)) = ζ.1 * v) : defect Q q U w = defect Q q U v := by
  have hq0 : q ≠ 0 := fun h0 => NeZero.ne Q (Nat.eq_zero_of_zero_dvd (h0 ▸ hqQ))
  haveI : NeZero q := ⟨hq0⟩
  obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
  have h1 : kumT Q U w = kumT Q U v + resGen 1 ζ := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting Q).2 U ζ v w h
  have h2 : (redMap Q q 1).app U 0 (resGen 1 ζ) = resGen 1 ξ := GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ 1 U ζ ξ hξ
  have h3 : ((w ^ (Q / q) : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ξ.1 * ((v ^ (Q / q) : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) := by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h, hξ, mul_pow]
  have h4 : kumT q U (w ^ (Q / q)) = kumT q U (v ^ (Q / q)) + resGen 1 ξ :=
    (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 U ξ _ _ h3
  unfold defect
  rw [h1, h4, map_add, h2]
  abel

theorem defect_mul_prim_pow (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (v : (Γ(U, ⊤))ˣ) (a : ℕ) : ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v →
      defect Q q U w = defect Q q U v := by
  have hζ : IsUnit ζ.1 := IsUnit.of_pow_eq_one ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).1 ζ) (NeZero.ne Q)
  induction a with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    rw [Units.ext hw]
  | succ a ih =>
    intro w hw
    have e : ((hζ.unit ^ a * v : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ζ.1 ^ a * v := by simp
    rw [defect_mul_prim Q q hqQ U ζ (hζ.unit ^ a * v) w (by rw [hw, e, pow_succ]; ring)]
    exact ih _ e

end GlobalTheory.EtC.RedChern

namespace GlobalTheory.EtC.RedChern

theorem defect_eq_of_pow_eq (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ)
    (hQ : IsUnit (Q : Γ(U, ⊤))) (hvw : v ^ Q = w ^ Q) : defect Q q U v = defect Q q U w := by
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) ((res _ (tw q 1)).X 0) U).1 _ _ ?_
  refine loc_bind ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).1 hQ) fun V g hV => ?_
  obtain ⟨ζ⟩ := hV
  set v' : (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom v
  set w' : (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom w
  have hx : (((w' * v'⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤))) ^ Q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ← map_pow, ← map_pow, ← hvw, mul_inv_cancel, Units.val_one]
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.1 ζ _ hx) fun W k ⟨a, ha⟩ => ?_
  rw [GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W U (k ≫ g) v hQ, GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W U (k ≫ g) w hQ]
  symm
  refine defect_mul_prim_pow Q q hqQ W (ζ.map k.appTop.hom) _ a _ ?_
  have e1 : ∀ u : (Γ(U, ⊤))ˣ, ((Units.map (k ≫ g).appTop.hom.toMonoidHom u : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      k.appTop.hom ((Units.map g.appTop.hom.toMonoidHom u : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) := fun u => rfl
  rw [e1, e1]
  change k.appTop.hom (w' : Γ(V, ⊤)) = (k.appTop.hom ζ.1) ^ a * k.appTop.hom (v' : Γ(V, ⊤))
  rw [← ha, ← map_mul, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end GlobalTheory.EtC.RedChern
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → v ^ Q = w ^ Q → GlobalTheory.EtC.RedChern.defect Q q U v = GlobalTheory.EtC.RedChern.defect Q q U w := by
  atlas_forward_decl GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

private theorem unitsMap_comp_appTop {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) := by
  ext
  simp [Scheme.Hom.comp_appTop]
  rfl

private theorem isUnit_natCast_appTop {V U : Scheme.{0}} (g : V ⟶ U) (Q : ℕ) (h : IsUnit (Q : Γ(U, ⊤))) :
    IsUnit (Q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem res_defectSec : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) →
    ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u →
      Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defect Q q V v := by
  intro Q q _ hqQ U u hQ

  let S : Sieve U :=
    { arrows := fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ Q = Units.map g.appTop.hom.toMonoidHom u
      downward_closed := by
        rintro V W g ⟨v, hv⟩ k
        refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
        rw [← map_pow, hv, unitsMap_comp_appTop] }
  have hS : S ∈ Scheme.etaleTopology U := by
    obtain ⟨S₀, hS₀, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u
    exact GrothendieckTopology.superset_covering _ (fun V g hg => hP V g hg) hS₀
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res _ (tw q 1)).X 0) V :=
    fun V g hg => defect Q q V hg.choose
  have hcompat : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k) := by
    intro V W g k hg
    have hQV : IsUnit (Q : Γ(V, ⊤)) := isUnit_natCast_appTop g Q hQ
    have hQW : IsUnit (Q : Γ(W, ⊤)) := isUnit_natCast_appTop k Q hQV
    change Sec.res k (defect Q q V hg.choose) = defect Q q W (S.downward_closed hg k).choose
    rw [GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W V k hg.choose hQV]
    refine GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq Q q hqQ W _ _ hQW ?_
    rw [(S.downward_closed hg k).choose_spec, ← map_pow, hg.choose_spec, unitsMap_comp_appTop]
  obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).2 S hS s hcompat
  have hex : ∃ a : Sec ((res _ (tw q 1)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ),
      v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = defect Q q V v := by
    refine ⟨a, fun V g v hv => ?_⟩
    have hg : S.arrows g := ⟨v, hv⟩
    rw [ha V g hg]
    exact GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq Q q hqQ V _ _ (isUnit_natCast_appTop g Q hQ) (hg.choose_spec.trans hv.symm)
  intro V g v hv
  exact pick_spec hex V g v hv

end GlobalTheory.EtC.RedChern
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_restrict : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defect Q q V v := by
  atlas_forward_decl GlobalTheory.EtC.RedChern.res_defectSec
end
