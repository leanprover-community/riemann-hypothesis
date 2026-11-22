module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMonHomIdPow
public import Development.AbelianVarietyTheory.Definitions.Divisors.NontrivialOfArtinQE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemOfMemHeckeLevel
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.W2

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.HodgeCoh
open GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.HeckeCorr
open scoped TensorProduct

section Side

variable {Γ : Type} [Group Γ]

theorem mem_heckeLevel_inv {K : Subgroup Γ} {h u : Γ} : u ∈ heckeLevel K h⁻¹ ↔ u ∈ K ∧ h * u * h⁻¹ ∈ K := by
  refine ⟨fun hu => ⟨heckeLevel_le K h⁻¹ hu, by simpa using conj_mem_of_mem_heckeLevel hu⟩, fun hu => ⟨hu.1, ?_⟩⟩
  exact ⟨h * u * h⁻¹, hu.2, by simp [MulAut.conj_apply, _root_.mul_assoc]⟩

end Side

section Corr

variable {G₀ : GDatum} {gb : GBase G₀ ℂ}

namespace Corr

variable {N N' : ℕ} {X : GenModel gb N} {X' : GenModel gb N'} (C : Corr X X') (k : ℕ)

end Corr

end Corr

section Relevel

variable {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G₀ R} {N M : ℕ}

end Relevel

section Wit

variable {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : _root_.GlobalTheory.LKGeo.Link D G) {gb : GBase D.toG R}

theorem smul_mem_laHat {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a', x, ha', rfl⟩ := hu
    refine AddSubgroup.subset_closure ⟨a * a', x, fun w => ?_, by rw [TensorProduct.smul_tmul', smul_eq_mul]⟩
    rw [map_mul]
    exact mul_mem (ha w) (ha' w)
  | zero => rw [smul_zero]; exact zero_mem _
  | add u u' _ _ hu hu' => rw [smul_add]; exact add_mem hu hu'
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

def scalarAf (G : HTGroup p) (a : (AfP p)ˣ) : G.GAf :=
  ⟨(Units.map (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)).toMonoidHom a, a * a), by
    show algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a * (starT G.star (AfP p) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a)).unop =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) ((a : AfP p) * a)
    have e : algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a = (a : AfP p) ⊗ₜ[ℚ] (1 : G.C) := rfl
    rw [map_mul, e, starT_tmul, map_one, MulOpposite.unop_one]⟩

theorem actG_scalarAf (a : (AfP p)ˣ) (v : AfP p ⊗[ℚ] VQ D) : L.actG (scalarAf G a) v = (a : AfP p) • v := by
  show actOn L.rep (AfP p) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a) v = _
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

theorem scalarAf_comm (a : (AfP p)ˣ) (u : G.GAf) : scalarAf G a * u = u * scalarAf G a :=
  Subtype.ext (Prod.ext (Units.ext (Algebra.commutes (a : AfP p) _)) (mul_comm _ _))

def natUnit (p : ℕ) (c : ℕ) (hc : c ≠ 0) : (AfP p)ˣ :=
  Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 (c : ℚ) (Nat.cast_ne_zero.2 hc))

theorem actG_natScalar (c : ℕ) (hc : c ≠ 0) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG (scalarAf G (natUnit p c hc)) v = c • v := by
  rw [actG_scalarAf]
  show algebraMap ℚ (AfP p) (c : ℚ) • v = _
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

end Wit

section Op

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : _root_.GlobalTheory.LKGeo.Link D G) {gb : GBase D.toG ℂ} {N : ℕ}

theorem relIndex_KN_ne_zero {N N' : ℕ} (hN : 0 < N) (hN' : 0 < N') : (L.KN N').relIndex (L.KN N) ≠ 0 := by
  obtain ⟨K, hK⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N hN
  obtain ⟨K', hK'⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N' hN'
  haveI : CompactSpace (L.KN N) := isCompact_iff_compactSpace.1 (hK ▸ K.compact)
  have ho : IsOpen ((L.KN N').subgroupOf (L.KN N) : Set (L.KN N)) :=
    (show IsOpen (L.KN N' : Set G.GAf) from hK' ▸ K'.K.isOpen).preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'

theorem KN_mul_le (N k' : ℕ) : L.KN (N * k') ≤ L.KN N := by
  have key : ∀ g, L.CongOne (N * k') g → L.CongOne N g := fun g hg v hv => by
    obtain ⟨w, hw, e⟩ := hg v hv
    exact ⟨k' • w, nsmul_mem hw k', by rw [e, mul_smul]⟩
  exact fun g hg => ⟨key _ hg.1, key _ hg.2⟩

variable {L}

end Op

section Away

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

variable (L : _root_.GlobalTheory.LKGeo.Link D G)

end Away

section Basic₂

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : _root_.GlobalTheory.LKGeo.Link D G) {gb : GBase D.toG ℂ} {N : ℕ}

end Basic₂

end GlobalTheory.W2
