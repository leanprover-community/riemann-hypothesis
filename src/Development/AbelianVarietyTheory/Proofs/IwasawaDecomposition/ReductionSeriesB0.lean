import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterGridData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCuspMultiplicityInputStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingsCharactersClassGroups
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideDataOverSetLevelsStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList

section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial

theorem exists_basis_coord_lattice {O V : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
    (B : Submodule O V) (hfg : B.FG)
    (hsp : Submodule.span (FractionRing O) (B : Set V) = ⊤) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) (FractionRing O) V),
      ∀ f : V, f ∈ B ↔ ∀ t, e.repr f t ∈ (algebraMap O (FractionRing O)).range := by
  classical
  have hfin : Module.Finite O B := Module.Finite.iff_fg.2 hfg
  have htf : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O (FractionRing O) V
  have hfree : Module.Free O B := inferInstance
  let bO := Module.finBasis O B
  let v : Fin (Module.finrank O B) → V := fun t => (bO t : V)
  have hliO : LinearIndependent O v := bO.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hliK : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hliO
  have hBspan : B = Submodule.span O (Set.range v) := by
    have h1 : Submodule.map B.subtype (Submodule.span O (Set.range bO)) = B := by
      rw [bO.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact h1.symm
  have hle : (⊤ : Submodule (FractionRing O) V) ≤ Submodule.span (FractionRing O) (Set.range v) := by
    rw [← hsp, Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span O (Set.range v) := hBspan ▸ hx
    exact Submodule.span_subset_span O (FractionRing O) (Set.range v) hx'
  let e := Module.Basis.mk hliK hle
  have he : ∀ t, e t = v t := fun t => by simp [e]
  refine ⟨_, e, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · rw [hBspan] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      intro s
      rw [← he, e.repr_self]
      by_cases h : t = s
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩
    | zero => intro s; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro s
      rw [map_add, Finsupp.add_apply]
      exact add_mem (hx s) (hy s)
    | smul a x _ hx =>
      intro s
      rw [← algebraMap_smul (FractionRing O) a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem ⟨a, rfl⟩ (hx s)
  · choose c hc using hf
    rw [← e.sum_repr f]
    refine sum_mem fun t _ => ?_
    rw [← hc t, algebraMap_smul, he]
    exact B.smul_mem _ (hBspan ▸ Submodule.subset_span ⟨t, rfl⟩)

section SideCoord

variable {K C : Type} [Field K] [Field C] (iC : K →+* C) {V : Bool → Type}
  [∀ b, AddCommGroup (V b)] [∀ b, Module K (V b)] {n : Bool → ℕ}
  (e : ∀ b, Module.Basis (Fin (n b)) K (V b))

def sideEv (b : Bool) : V b →+ ((Σ b', Fin (n b')) → C) where
  toFun f y := if h : y.1 = b then iC ((e b).repr f (h ▸ y.2)) else 0
  map_zero' := by
    funext y
    by_cases h : y.1 = b <;> simp [h]
  map_add' f g := by
    funext y
    by_cases h : y.1 = b <;> simp [h]

@[simp] theorem sideEv_same (b : Bool) (f : V b) (t : Fin (n b)) :
    sideEv iC e b f ⟨b, t⟩ = iC ((e b).repr f t) := by
  simp [sideEv]

theorem sideEv_other {b b' : Bool} (h : b' ≠ b) (f : V b) (t : Fin (n b')) :
    sideEv iC e b f ⟨b', t⟩ = 0 := by
  simp [sideEv, h]

theorem sideEv_smul (b : Bool) (a : K) (f : V b) (y : Σ b', Fin (n b')) :
    sideEv iC e b (a • f) y = iC a * sideEv iC e b f y := by
  obtain ⟨b', t⟩ := y
  by_cases h : b' = b
  · subst h; simp
  · simp [sideEv_other iC e h]

theorem sideEv_inj (b : Bool) : Function.Injective (sideEv iC e b) := by
  intro f g hfg
  apply (e b).repr.injective
  ext t
  have := congrFun hfg ⟨b, t⟩
  exact iC.injective (by simpa using this)

def sideU (b : Bool) (T : Module.End K (V b)) (c y : Σ b', Fin (n b')) : C :=
  if h : c.1 = b then sideEv iC e b (T (e b (h ▸ c.2))) y else 0

theorem sideEv_end (b : Bool) (T : Module.End K (V b)) (f : V b) (y : Σ b', Fin (n b')) :
    sideEv iC e b (T f) y = ∑ c, sideU iC e b T c y * sideEv iC e b f c := by
  classical
  have h0 : T f = ∑ t, (e b).repr f t • T (e b t) := by
    conv_lhs => rw [← (e b).sum_repr f]
    simp only [map_sum, map_smul]
  have h1 : sideEv iC e b (T f) y =
      ∑ t, iC ((e b).repr f t) * sideEv iC e b (T (e b t)) y := by
    rw [h0, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => sideEv_smul iC e b _ _ y
  rw [h1, Fintype.sum_sigma, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [sideU, mul_comm]
  · intro b' _ hb
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [sideEv_other iC e hb]
  · simp

end SideCoord

theorem exists_nth_of_fg_full : ∀ (D : D7) (tw : NTw D.R D.host D.what₂ D.LL0 D.nd)
    (ex : NExp D.R D.host D.what₂ D.LL0 D.nd tw),
    (∀ i : tw.Tw, ∃ iC : FractionRing (tw.O i) →+* ℂ_[tw.l i], ∀ x, ‖iC x‖ ≤ 1 ↔
      x ∈ (algebraMap (tw.O i) (FractionRing (tw.O i))).range) →
    (∀ i j b, (ex.Bsup i j b).FG ∧
      Submodule.span (FractionRing (tw.O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) →
    Nonempty (NTh D.R D.host D.what₂ D.LL0 D.nd tw ex) := by
  classical
  intro D tw ex hi hB
  choose iC hiC using hi
  have hex := fun i j b =>
    exists_basis_coord_lattice (ex.Bsup i j b) (hB i j b).1 (hB i j b).2
  choose n e he using hex
  have hsup : ∀ i j b, {f : ex.Fm i j b | f ∈ (⊤ : AddSubgroup (ex.Fm i j b)) ∧
      ∀ y, ‖sideEv (iC i) (e i j) b f y‖ ≤ 1} = (ex.Bsup i j b : Set (ex.Fm i j b)) := by
    intro i j b
    ext f
    simp only [Set.mem_ofPred_eq, AddSubgroup.mem_top, true_and, SetLike.mem_coe]
    rw [he i j b f]
    constructor
    · intro h t
      have := h ⟨b, t⟩
      rw [sideEv_same] at this
      exact (hiC i _).1 this
    · intro h y
      obtain ⟨b', t⟩ := y
      by_cases hb : b' = b
      · subst hb
        rw [sideEv_same]
        exact (hiC i _).2 (h t)
      · rw [sideEv_other _ _ hb]
        simp
  exact ⟨{
    iC := iC
    iC_int := hiC
    aL := fun i => if ∃ k, tw.l i = D.host.g k then 1 else 0
    aL_g := fun i k h => if_pos ⟨k, h⟩
    aL_off := fun i h => if_neg (not_exists.2 h)
    Pt := fun i j => Σ b, Fin (n i j b)
    ev := fun i j b => sideEv (iC i) (e i j) b
    ev_smul := fun i j b a f y => sideEv_smul _ _ b a f y
    ev_inj := fun i j b => sideEv_inj _ _ b
    Lt := fun _ _ => PUnit
    acgLt := fun _ _ => inferInstance
    modLt := fun _ _ => inferInstance
    freeLt := fun _ _ => inferInstance
    finLt := fun _ _ => inferInstance
    Let := fun _ _ => PEmpty
    finLet := fun _ _ => inferInstance
    Harm := fun _ _ => Set.univ
    Ctr := fun _ _ => PEmpty
    ctrC := fun _ _ κ => κ.elim
    Harm_def := fun i j P => ⟨fun _ κ => κ.elim, fun _ => Set.mem_univ _⟩
    thV := fun _ _ _ _ _ => 0
    thV_add := fun _ _ _ _ _ _ => by simp
    thV_smul := fun _ _ _ _ _ _ => by simp
    thV_addP := fun _ _ _ _ _ _ => by simp
    thV_smulP := fun _ _ _ _ _ _ => by simp
    datPhi := fun _ _ _ _ => 0
    datP := fun _ _ _ _ => 0
    recDet := fun _ _ _ => 1
    Kq := fun _ _ _ => PUnit
    grpKq := fun _ _ _ => inferInstance
    actK := fun _ _ _ _ y => y
    actK_one := fun _ _ _ _ => rfl
    actK_mul := fun _ _ _ _ _ _ => rfl
    recDetq := fun _ _ _ _ => 1
    recDetq_mem := fun _ _ _ _ => one_mem _
    recDet_act := fun _ _ _ _ _ _ _ _ _ _ => rfl
    recDetq_act := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    hkIdx := fun i j _ _ => Σ b, Fin (n i j b)
    finHk := fun _ _ _ _ => inferInstance
    hkMove := fun _ _ _ _ c _ => c
    hkU := fun i j b k P c y => sideU (iC i) (e i j) b (ex.hkF i j b k P) c y
    hk_ev := fun i j b k P _ _ _ _ f y => sideEv_end _ _ b _ f y
    MaximalUnramifiedExtension := fun _ => ⊤
    FmUr := fun _ _ _ => ⊤
    FmUr_smul := fun _ _ _ _ _ _ _ => AddSubgroup.mem_top _
    FmUr_span := fun i j b => by
      rw [AddSubgroup.coe_top, Submodule.span_univ]
    Bsup_def := fun i j b => by
      rw [hsup i j b, Submodule.span_eq] }⟩

end GlobalTheory.HeightCounting

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Df

open Formalism.L2.TwC

theorem norm_le_one_of_mem_clC' (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) {z : ℂ_[l]}
    (hz : z ∈ clC l F) : ‖z‖ ≤ 1 := by
  have hm : z ∈ PadicComplexInt l := (Subring.mem_inf.1 hz).2
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff] at hm
  rw [PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).2 hm

theorem exists_iC_of_clC (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (e : O ≃+* clC l F)
    (hratio : ∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) :
    ∃ iC : FractionRing O →+* ℂ_[l],
      ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  let ψ : O →+* ℂ_[l] := (clC l F).subtype.comp e.toRingHom
  have hψ : Function.Injective ψ := fun a b h => e.injective (Subtype.ext h)
  let iC : FractionRing O →+* ℂ_[l] := IsFractionRing.lift hψ
  have hiC : ∀ a : O, iC (algebraMap O (FractionRing O) a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψ a
  refine ⟨iC, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    have hb0 : algebraMap O (FractionRing O) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hψb : ψ b ≠ 0 := by
      rw [← hiC]; exact (map_ne_zero iC).2 hb0
    rw [map_div₀, hiC, hiC, norm_div, div_le_one (norm_pos_iff.2 hψb)] at hx
    have hmem := hratio _ (e a).2 _ (e b).2 hx
    refine ⟨e.symm ⟨_, hmem⟩, ?_⟩
    apply iC.injective
    rw [hiC, map_div₀, hiC, hiC]
    show ((e (e.symm ⟨_, hmem⟩) : clC l F) : ℂ_[l]) = _
    rw [e.apply_symm_apply]
    rfl
  · rintro ⟨a, rfl⟩
    rw [hiC]
    exact norm_le_one_of_mem_clC' l F (e a).2

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

open Formalism.L2.TwC

end GlobalTheory.Mem.Df
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem GlobalTheory.LamTie.cond0_primes_lowAll : ∀ (D : D7) (Z : GlobalTheory.LamTie.LamDat D), Z.Ok → Z.q0 = AbsolutelyIrreducibleSpan.q0 D → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → ∃ p ∈ lowAll D, P ∈ placesOver D.host.E p := by
  intro D Z hZ hq P hP
  have hPr : Prime (GlobalTheory.ToricDenom.below P).asIdeal := (GlobalTheory.ToricDenom.below P).prime

  have key : ∀ n : ℕ, ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) →
      ((n : 𝓞 D.host.E) ∈ P.asIdeal) := by
    intro n hn
    have h1 : algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal := hn
    simpa using h1
  have key' : ∀ n : ℕ, ((n : 𝓞 D.host.E) ∈ P.asIdeal) →
      ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) := by
    intro n hn
    show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal
    simpa using hn
  unfold GlobalTheory.LamTie.cond0 at hP
  rcases hPr.dvd_or_dvd hP with h | h
  · have h2 := hPr.dvd_of_dvd_pow h
    rw [Ideal.dvd_span_singleton] at h2
    have h3 := key _ (by exact_mod_cast h2)
    push_cast at h3
    have hpr := P.isPrime
    rcases hpr.mem_or_mem h3 with h4 | h4
    · rcases hpr.mem_or_mem h4 with h5 | h5
      · rcases hpr.mem_or_mem h5 with h6 | h6
        · exact ⟨D.host.g 0, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
        · exact ⟨D.host.g 1, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
      · exact ⟨D.host.pde, by simp [GlobalTheory.HeightCounting.lowAll], h5⟩
    · exact ⟨D.host.pde', by simp [GlobalTheory.HeightCounting.lowAll], h4⟩
  · have hle : (GlobalTheory.ToricDenom.below Z.w0).asIdeal ≤ (GlobalTheory.ToricDenom.below P).asIdeal :=
      Ideal.le_of_dvd h
    have heq : (GlobalTheory.ToricDenom.below Z.w0).asIdeal = (GlobalTheory.ToricDenom.below P).asIdeal :=
      ((GlobalTheory.ToricDenom.below Z.w0).isMaximal).eq_of_le (GlobalTheory.ToricDenom.below P).isPrime.ne_top hle
    have hw : ((Z.q0 : ℕ) : 𝓞 D.host.E) ∈ Z.w0.asIdeal := hZ.places.referencePlaceOverPrime
    have hb : ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below Z.w0).asIdeal := by
      show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ Z.w0.asIdeal
      simpa using hw
    rw [heq] at hb
    refine ⟨Z.q0, ?_, key _ hb⟩
    rw [hq]
    simp [GlobalTheory.HeightCounting.lowAll, lowPr]
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_primes_in_low_set : ∀ (D : D7) (Z : GlobalTheory.LamTie.LamDat D), Z.Ok → Z.q0 = AbsolutelyIrreducibleSpan.q0 D → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → ∃ p ∈ lowAll D, P ∈ placesOver D.host.E p := by
  atlas_forward_decl GlobalTheory.LamTie.cond0_primes_lowAll
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem exists_Sx (D : D7) : ∃ Sx : Finset (PlE D.host), (∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑Sx) ∧
    OverSet D Sx (lowAll D) ∧ (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) := by
  have hne : ∀ p ∈ lowAll D, p ≠ 0 := by
    intro p hp
    simp only [lowAll, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl
    · exact lowPr_ne_zero D p hp
    · exact (D.host.g_prime 0).ne_zero
    · exact (D.host.g_prime 1).ne_zero
    · exact D.host.pde_prime.ne_zero
    · exact D.host.pde'_prime.ne_zero
  have hfin : (⋃ p ∈ (lowAll D : Set ℕ), placesOver D.host.E p).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => Formalism.L2.TwC.placesOver_finite' D.host.E p (hne p hp)
  refine ⟨hfin.toFinset, fun p hp Q hQ => ?_, fun Q hQ => ?_, fun Q Q' hQ hc => ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 hp) hQ
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact ⟨p, hp, hQp⟩
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact (Set.Finite.mem_toFinset hfin).2 (Set.mem_biUnion hp (placesOver_conj D p hQp hc))

open Formalism.L2.TwC in

theorem pointwise (hPr : PrN) (hSer : SerN) (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) {K : Ctx} {B : Base}
    {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : LI hL x)
    (G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩)
    (hF : GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x))) (hOk : (GlobalTheory.BigTop.Fun.lamOf G).Ok)
    (hC : (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x) (hq : (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x)) :
    ∃ x' : St P, Nonempty (SettingsLevel hL x') ∧ ListSt cDep x' := by
  have hgal : GalEx (Dof x) :=
    GlobalTheory.HeightCounting.galEx_of_cgTrue hL hPr.what₂.fin hPr.what₂.gal (Dof x) l.a.A.wdT ⟨l.a.cg⟩
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb (Dof x)
  obtain ⟨c0f, hf⟩ := GlobalTheory.T.row_cusp_multiplicity_input hPr.what₂.art (Dof x) (cfOf x) l.a.jE l.a.A l.rat.S l.rat.In (lowAll (Dof x)) l.Pq
    l.mt.M _ (QOf P) l.mt.mt l.Pq_over hgal l.cusp hcheb l.a.elem.star l.a.elem.int l.a.elem.split
  have hJ := fun (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ↥(Dof x).LL0))
      (hv : ((p : ℕ) : 𝓞 ↥(Dof x).LL0) ∈ v.asIdeal) => Formalism.BasicNotions.Examples₂.LB.exists_embAt (l := p) v hv
  obtain ⟨c0r, hr⟩ := GlobalTheory.T.exists_twistRings_characters_classGroups hPr.what₂.art (Dof x) (cfOf x) (fun p _ v hv => (hJ p v hv).choose)
    (fun p _ v hv y => (hJ p v hv).choose_spec y) l.a.val l.a.elem.star l.a.elem.int
  let b0 : Big (Dof x) := fun p _ j =>
    ⟨(c0f p j).1 ⊔ (c0r p j).1, by haveI := (c0f p j).2; haveI := (c0r p j).2; infer_instance⟩
  obtain ⟨Sx, hSx1, hSx2, hSx3⟩ := exists_Sx (Dof x)
  obtain ⟨T', Sp, -⟩ := hr b0 b0 Sx (fun p _ j => le_sup_right)
  have hSbSx : l.rat.In.Sb ⊆ Sx := l.rat.rat.Sb_le.subset hSx1
  obtain ⟨F, ex, h0, hfg, hsb⟩ := hf b0 b0 Sx T' Sp (fun p _ j => le_sup_left) hSbSx hSx3 hSx1
  have hSxS0 : ∀ i, ∀ Q ∈ Sx, Q ∈ T'.S0 i := fun i Q hQ => by
    have h := Sp.ringSpec_excludedPlaces_eq i
    have : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := by
      rw [h]; exact Or.inr (Finset.mem_coe.2 hQ)
    exact Finset.mem_coe.1 this
  have hratio : ∀ i, ∀ y ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)),
      ∀ z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)), ‖y‖ ≤ ‖z‖ →
        y / z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)) := fun i => by
    have h := GlobalTheory.CycClosure.exists_cyclotomic_integers (T'.l i) (Sp.K0 i) (Sp.Lw i) 0
    have h0 : Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) ⊔ muK (T'.l i) 0 = Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) := by
      rw [h.snd.2.2.2.2.1, sup_bot_eq]
    rw [h0] at h
    exact h.snd.2.2.2.1
  choose iC hiC using fun i => GlobalTheory.Mem.Df.exists_iC_of_clC (T'.l i) (T'.O i) _ (Sp.eO i) (hratio i)
  obtain ⟨L, hLam⟩ := GlobalTheory.T.exists_toricCharacters_in_twistCoefficientRings hPr.what₂.cheb hPr.what₂.art hSer.ratio (Dof x) l.a.A.bare (cfOf x) l.a.A.row
    (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ b0 b0 Sx T' Sp (GlobalTheory.BigTop.Fun.lamOf G) hC hOk
    (GlobalTheory.BigTop.Fun.lamOf_teich G) l.a.val (fun a => hF.values (a.1 + 1) (by omega) a.2)
    (fun i Q hQ => by
      obtain ⟨p, hp, hQp⟩ := GlobalTheory.T.conductor_primes_in_low_set (Dof x) _ hOk hq Q hQ
      exact hSxS0 i Q (Finset.mem_coe.1 (hSx1 p hp hQp)))
  obtain ⟨htie, hside⟩ := hLam F
  obtain ⟨th0⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F (TwL.empty T')) ex
    (fun i => ⟨iC i, hiC i⟩) hfg
  obtain ⟨th1⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F L) { ex with }
    (fun i => ⟨iC i, hiC i⟩) hfg
  have hB := hside ex h0 th0 (hsb th0) th1
  refine GlobalTheory.T.side_data_over_set_levels hL cDep x l ⟨T'.ntw l.a.A.bare F L, { ex with }, h0, th1, Sp.br, Sp.br_ind⟩ hB
    (fun i => hSbSx.trans fun Q hQ => hSxS0 i Q hQ) (fun i Q hQ => ?_) G hF hOk hC hq htie
  have h := Sp.ringSpec_excludedPlaces_eq i
  have hQ' : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := Finset.mem_coe.2 hQ
  rw [h] at hQ'
  simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_coe] at hQ'
  rcases hQ' with (((h1 | ⟨k, h1⟩) | h1) | h1) | h1
  · exact ⟨_, Finset.mem_insert_self _ _, h1⟩
  · refine ⟨(Dof x).host.g k, Finset.mem_insert_of_mem ?_, h1⟩
    fin_cases k <;> simp [lowAll]
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · obtain ⟨p, hp, hQp⟩ := hSx2 Q h1
    exact ⟨p, Finset.mem_insert_of_mem hp, hQp⟩

theorem sb0l : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ cDep : ℝ, SettingsFormsExistList hL cDep := by
  intro hPr hSer hL cDep
  exact (GlobalTheory.T.exists_character_grid_data hPr cDep).trans (StepW.of_all fun K B f T w _ _ h P x l => by
    obtain ⟨G, hF, hOk, hC, hq⟩ := h P x
    exact pointwise hPr hSer hL cDep x l G hF hOk hC hq)

end GlobalTheory.HeightCounting.Up.PointwiseSettings
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.settingsFormsExistList_of_localLanglands : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ cDep : ℝ, SettingsFormsExistList hL cDep := by
  atlas_forward_decl GlobalTheory.HeightCounting.Up.PointwiseSettings.sb0l
end
