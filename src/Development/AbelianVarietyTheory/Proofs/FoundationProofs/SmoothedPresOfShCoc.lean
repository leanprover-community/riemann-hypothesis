import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleHodgeTateZetaClassParams
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFR2
import Development.AbelianVarietyTheory.Definitions.Foundations.ChiProj
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu
import Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialPrimitiveRootOfCyclotomicInertia
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsClosedInertiaCyclotomicKernel
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HtPresNu7MonoLoss
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KumUnit

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def ValPres (A : ValuationSubring Ω) (m r : ℕ) (ζ : Ω) (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (o : ι → Qbar l) (u : ι → Ω) (n : ι → ℤ) (k : ι → G ℚ Ω → ZMod (l ^ m)),
    (∀ i, ‖o i‖ ≤ 1) ∧ (∀ i, u i ≠ 0 ∧ A.valuation (u i) ^ (l ^ r).totient = A.valuation (l : Ω) ^ n i) ∧
    (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l r s = 1 →
      (∀ i, GlobalTheory.Col.KumVal (l := l) m ζ (u i) s (k i s)) ∧ Cg m (z s 1) (∑ i, o i * ((k i s).val : Qbar l))) ∧
    Cg m (∑ i, o i * (((n i : ZMod (l ^ m))).val : Qbar l)) 0

theorem cg_trans {m : ℕ} {x y z : Qbar l} (h : Cg m x y) (h' : Cg m y z) : Cg m x z := by
  unfold Cg at *
  have hm := IsUltrametricDist.norm_add_le_max (x - y) (y - z)
  rw [sub_add_sub_cancel] at hm
  exact hm.trans (max_le h h')

theorem cg_symm {m : ℕ} {x y : Qbar l} (h : Cg m x y) : Cg m y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

theorem cg_sum {m : ℕ} {ι : Type} (S : Finset ι) {x y : ι → Qbar l} (h : ∀ i ∈ S, Cg m (x i) (y i)) :
    Cg m (∑ i ∈ S, x i) (∑ i ∈ S, y i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) h

theorem cg_mul_left {m : ℕ} {o x y : Qbar l} (ho : ‖o‖ ≤ 1) (h : Cg m x y) : Cg m (o * x) (o * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖o‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right ho (norm_nonneg _)
    _ = ‖x - y‖ := one_mul _
    _ ≤ _ := h

end GlobalTheory.KumUnit
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ.UnitPres

open GlobalTheory.KumUnit

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem kumVal_int {n : ℕ} {ζ u v : Ω} {s : G ℚ Ω} {j : ℤ} (hζ : ζ ^ (l ^ n) = 1) (hv : v ^ (l ^ n) = u)
    (hs : s v = ζ ^ j * v) : GlobalTheory.Col.KumVal (l := l) n ζ u s (j : ZMod (l ^ n)) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have h0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hpos.ne'] at hζ; exact zero_ne_one hζ
  refine ⟨v, hv, ?_⟩
  rw [hs, ← zpow_natCast, ZMod.val_intCast]
  congr 1
  conv_lhs => rw [← Int.emod_add_mul_ediv j ((l ^ n : ℕ) : ℤ)]
  rw [zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

theorem cg_intCast (n : ℕ) (j : ℤ) : Cg (l := l) n (((j : ZMod (l ^ n)).val : ℕ) : Qbar l) (j : Qbar l) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have h1 : (((j : ZMod (l ^ n)).val : ℕ) : ℤ) - j = ((l ^ n : ℕ) : ℤ) * (-(j / ((l ^ n : ℕ) : ℤ))) := by
    rw [ZMod.val_intCast, Int.emod_def]; ring
  have e : (((j : ZMod (l ^ n)).val : ℕ) : Qbar l) - (j : Qbar l) =
      (l : Qbar l) ^ n * ((-(j / ((l ^ n : ℕ) : ℤ)) : ℤ) : Qbar l) := by
    have := congrArg (Int.cast : ℤ → Qbar l) h1
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_pow] at this
    exact this
  rw [Cg, e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one (Qbar l) _)

theorem exists_open [IsAlgClosure ℚ Ω] (h : G ℚ Ω → Qbar l) (hc : Continuous h) (h1 : h 1 = 0) (m : ℕ) :
    ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ s ∈ U, Cg m (h s) 0 := by
  have hl : (0 : ℝ) < ‖((l : ℕ) : Qbar l) ^ m‖ :=
    norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have hn : {s | ‖h s‖ < ‖((l : ℕ) : Qbar l) ^ m‖} ∈ nhds (1 : G ℚ Ω) :=
    (isOpen_lt hc.norm continuous_const).mem_nhds (by simpa [h1] using hl)
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 hn
  refine ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun s hs => ?_⟩
  rw [Cg, sub_zero]
  exact le_of_lt (hsub hs)

theorem layer_one {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {r : ℕ}
    {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer2 c A ν r z) : z 1 1 = 0 := by
  have h := hz.2 1 (one_mem _) 1 (one_mem _) 1
  rw [mul_one, map_one, inv_one, mul_one] at h
  have h' : (ν 1 : Qbar l) * z 1 1 = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h').resolve_left (ν 1).ne_zero

theorem layer_add {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {r : ℕ}
    {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer2 c A ν r z) {s t : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) A)
    (ht : t ∈ Dec (F := ℚ) A) (hc : cycMod ℚ Ω l r s = 1) : z (s * t) 1 = z s 1 + (ν s : Qbar l) * z t 1 := by
  have h := hz.2 s hs t ht 1
  rwa [hc, inv_one, mul_one] at h

end GlobalTheory.KZ.UnitPres
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.LambdaValuationPowers.AllRoots

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem pres_of_vanish (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → Z m s 1 = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A c m 0 Z ζ P o := by
  refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, hζ, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
  have h := GlobalTheory.Col.kumPres_empty A (n := m - 0) (r := m) (ζ := ζ ^ l ^ 0) (by simpa using hζ) (by omega) (Z m) hZ
  convert h using 2 <;> exact Empty.elim ‹_›

theorem continuous_of_cg [Algebra.IsAlgebraic ℚ Ω] (f : G ℚ Ω → Qbar l)
    (h : ∀ n : ℕ, ∃ E0 : Finset Ω, ∀ s s' : G ℚ Ω, (∀ z ∈ E0, s' z = z) → Cg n (f (s * s')) (f s)) : Continuous f := by
  have hnl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have hlt1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt1
  obtain ⟨E0, hE⟩ := h n
  have hopen : ∀ᶠ t in nhds (1 : G ℚ Ω), ∀ z ∈ E0, t z = z := by
    rw [Filter.eventually_all_finset]
    intro z _
    have ho := stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Ω) z
    exact ho.mem_nhds (one_mem _)
  have hcont : Filter.Tendsto (fun t : G ℚ Ω => s⁻¹ * t) (nhds s) (nhds 1) := by
    have := (continuous_const_mul s⁻¹).tendsto s
    rwa [inv_mul_cancel] at this
  filter_upwards [hcont.eventually hopen] with t ht
  have := hE s (s⁻¹ * t) ht
  rw [mul_inv_cancel_left, Cg, norm_pow, hnl] at this
  rw [dist_eq_norm]
  exact this.trans_lt hn

end GlobalTheory.LambdaValuationPowers.AllRoots
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.LambdaValuationPowers.Smooth

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_sub_sub {m : ℕ} {a b a' b' : Qbar l} (h : Cg m a a') (h' : Cg m b b') : Cg m (a - b) (a' - b') := by
  have e : a - b - (a' - b') = (a - a') + -(b - b') := by ring
  rw [Cg, e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h (by rw [norm_neg]; exact h'))

theorem isUnit_natCast_padic {d : ℕ} (hd : Nat.Coprime d l) : IsUnit (d : ℤ_[l]) := by
  have hlp : l.Prime := Fact.out
  by_contra h
  have h1 : ‖((d : ℤ) : ℤ_[l])‖ < 1 := by
    rw [← PadicInt.mem_nonunits]; simpa using h
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h1
  exact (Nat.Prime.coprime_iff_not_dvd hlp).1 hd.symm (Int.natCast_dvd_natCast.mp h1)

theorem smoothed_pres [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : OverL l A) (c : Coef l)
    (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (hL : ∀ r, Layer2 c A ν r (Z r)) (hc : ∀ r, Continuous fun s => Z r s 1)
    (hI : ∀ s ∈ Ine (F := ℚ) A, ν s = 1) (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l) (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m 0 (fun r s y => Z r s y - (d₀ : Qbar l) * Z r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)))
        ζ P o := by
  classical
  have hlp : l.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i =>
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_pos hlp.pos i).ne'⟩
    inferInstance
  have hpos : 0 < l ^ m := pow_pos hlp.pos _
  haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
  have hz := hL m
  set z := Z m with hzdef
  set uu := ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right m hd₀) with huu
  have hl : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hlv⟩ := hA
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker
  have hH : ∀ s, s ∈ H ↔ s ∈ Ine (F := ℚ) A ∧ cycMod ℚ Ω l m s = 1 := fun s => Iff.rfl
  have hfix : ∀ s, cycMod ℚ Ω l m s = 1 → s ζ = ζ := fun s hs =>
    GlobalTheory.Col.fix_of_cycMod le_rfl hs hζ.pow_eq_one

  have hu₀ := isUnit_natCast_padic (l := l) hd₀
  obtain ⟨ρ, hρ, hρc⟩ := GlobalTheory.CycInertia.exists_mem_Ine_toZModPow Ω l A hl hu₀.unit m
  rw [hu₀.unit_spec, map_natCast] at hρc
  have hρD : ρ ∈ Dec (F := ℚ) A := Ine_le_Dec A hρ
  have hρi : ρ⁻¹ ∈ Ine (F := ℚ) A := inv_mem hρ
  have hρζ : ρ ζ = ζ ^ d₀ := by
    have hspec : ρ ζ = ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l ρ : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω ρ) ζ hζ.pow_eq_one
    rw [hspec, hρc, ZMod.val_natCast, hζ.eq_orderOf, pow_mod_orderOf]
  have hcρ : (cycMod ℚ Ω l m ρ⁻¹)⁻¹ = uu := by
    rw [map_inv, inv_inv]
    exact Units.ext (by rw [huu, ZMod.coe_unitOfCoprime]; exact hρc)
  have z11 : z 1 1 = 0 := GlobalTheory.KZ.UnitPres.layer_one hz
  have key : ∀ s ∈ H, z s uu = z (ρ⁻¹ * s * ρ) 1 := by
    intro s hs
    obtain ⟨hsI, hsc⟩ := (hH s).1 hs
    have hsD := Ine_le_Dec A hsI
    have e1 := hz.2 ρ⁻¹ (inv_mem hρD) (s * ρ) (mul_mem hsD hρD) 1
    have e2 := hz.2 s hsD ρ hρD uu
    have e3 := hz.2 ρ⁻¹ (inv_mem hρD) ρ hρD 1
    rw [hcρ] at e1 e3
    rw [inv_mul_cancel, z11, hI _ hρi, Units.val_one, one_mul, one_mul] at e3
    rw [hI _ hρi, Units.val_one, one_mul, one_mul] at e1
    rw [hI _ hsI, Units.val_one, one_mul, hsc, inv_one, mul_one] at e2
    rw [mul_assoc]
    linear_combination -e1 - e2 + e3
  have hHρ : ∀ s ∈ H, ρ⁻¹ * s * ρ ∈ H := fun s hs => by
    obtain ⟨hsI, hsc⟩ := (hH s).1 hs
    refine (hH _).2 ⟨?_, ?_⟩
    · have := conj_mem_Ine (inv_mem hρD) hsI
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, hsc, mul_one, map_inv, inv_mul_cancel]
  obtain ⟨ι, hι, o, crd, ho, hadd, hzero, hcrd, -⟩ := GlobalTheory.CoefCoord.coord_mod_pow l c m
  obtain ⟨U, hU, hUz⟩ := GlobalTheory.KZ.UnitPres.exists_open (fun s => z s 1) (hc m) z11 m
  have hex : ∀ i, ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ H, s u = u) ∧
      ∀ s ∈ H, GlobalTheory.Col.KumVal (l := l) m ζ u s (crd (z s 1) i) := fun i =>
    GlobalTheory.KumFix.exists_kumVal l Ω m H (GlobalTheory.isClosed_Ine_inf_ker_cycMod l Ω A _) ζ hζ
      (fun s hs => hfix s hs.2) (fun s => crd (z s 1) i)
      (fun s hs t ht => by
        show crd (z (s * t) 1) i = crd (z s 1) i + crd (z t 1) i
        rw [GlobalTheory.KZ.UnitPres.layer_add hz (Ine_le_Dec A hs.1) (Ine_le_Dec A ht.1) hs.2, hI s hs.1, Units.val_one, one_mul,
          hadd _ (hz.1 _ _) _ (hz.1 _ _), Pi.add_apply])
      U hU (fun s _ hs => by
        show crd (z s 1) i = 0
        rw [hzero _ (hz.1 _ _) (hUz s hs), Pi.zero_apply])
  choose u hu0 hufix huk using hex

  have hw0 : ∀ i, u i * (ρ (u i))⁻¹ ≠ 0 := fun i =>
    mul_ne_zero (hu0 i) (inv_ne_zero ((map_ne_zero ρ).2 (hu0 i)))
  have hvw : ∀ i, A.valuation (u i * (ρ (u i))⁻¹) = 1 := fun i => by
    rw [map_mul, map_inv₀, GlobalTheory.TameLabels.valuation_apply_of_mem_Dec hρD, mul_inv_cancel₀]
    exact (Valuation.ne_zero_iff _).2 (hu0 i)
  have hwfix : ∀ i, ∀ s ∈ H, s (u i * (ρ (u i))⁻¹) = u i * (ρ (u i))⁻¹ := fun i s hs => by
    have e : s (ρ (u i)) = ρ ((ρ⁻¹ * s * ρ) (u i)) := by
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]; congr 1; group
    rw [map_mul, map_inv₀, hufix i s hs, e, hufix i _ (hHρ s hs)]
  have hP : ∀ i, ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧
      P.eval ζ = u i * (ρ (u i))⁻¹ := fun i =>
    GlobalTheory.CycIne.exists_poly_of_fixed l Ω A hA m ζ hζ _ ((A.valuation_le_one_iff _).1 (hvw i).le)
      (fun s h1 h2 => hwfix i s ((hH s).2 ⟨h1, h2⟩))
  choose P hPc hPe using hP
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpos.ne'

  have hkw : ∀ s ∈ H, ∀ i, GlobalTheory.Col.KumVal (l := l) m ζ (u i * (ρ (u i))⁻¹) s
      ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : ZMod (l ^ m)) := by
    intro s hs i
    obtain ⟨v, hv, hsv⟩ := huk i s hs
    obtain ⟨v', hv', hsv'⟩ := huk i _ (hHρ s hs)
    refine GlobalTheory.KZ.UnitPres.kumVal_int hζ.pow_eq_one (v := v * (ρ v')⁻¹) ?_ ?_
    · rw [mul_pow, inv_pow, ← map_pow, hv', hv]
    · have e : s (ρ v') = ρ ((ρ⁻¹ * s * ρ) v') := by
        rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]; congr 1; group
      rw [map_mul, map_inv₀, hsv, e, hsv', map_mul, map_pow, hρζ, zpow_sub₀ hζ0, zpow_mul]
      simp only [zpow_natCast]
      ring
  refine ⟨ι, hι, P, o, hζ, hPc, fun i => (ho i).1, fun i => by rw [hPe]; exact hw0 i, ?_⟩
  show GlobalTheory.Col.KumPres A m m (ζ ^ l ^ 0) _ _ _
  rw [pow_zero, pow_one]
  refine ⟨hζ, le_rfl, fun i => ?_, fun i => (ho i).2, fun s hs hc' _ => ?_⟩
  · simp only [hPe]
    refine ⟨(A.valuation_le_one_iff _).1 (hvw i).le, hw0 i, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, hvw i, inv_one]
  · have hsH : s ∈ H := (hH s).2 ⟨hs, hc'⟩
    refine ⟨fun i => ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : ZMod (l ^ m)),
      fun i => by simp only [hPe]; exact hkw s hsH i, ?_⟩
    show Cg m (z s 1 - (d₀ : Qbar l) * z s (1 * uu)) _
    rw [one_mul, key s hsH]
    have h2 := hcrd _ (hz.1 s 1)
    have h3 := hcrd _ (hz.1 (ρ⁻¹ * s * ρ) 1)
    have h4 := cg_sub_sub h2 (GlobalTheory.KumUnit.cg_mul_left (o := (d₀ : Qbar l)) (IsUltrametricDist.norm_natCast_le_one (Qbar l) d₀) h3)
    refine GlobalTheory.KumUnit.cg_trans h4 (GlobalTheory.KumUnit.cg_symm (GlobalTheory.KumUnit.cg_trans
      (GlobalTheory.KumUnit.cg_sum _ fun i _ => GlobalTheory.KumUnit.cg_mul_left (ho i).2 (GlobalTheory.KZ.UnitPres.cg_intCast _ _)) ?_))
    have e : (∑ i, o i * ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : Qbar l)) =
        (∑ i, o i * ((crd (z s 1) i).val : Qbar l)) - (d₀ : Qbar l) * ∑ i, o i * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : Qbar l) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [e, Cg, sub_self, norm_zero]
    exact norm_nonneg _

theorem smoothed_pres_of_shCoc [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : OverL l A) (c : Coef l)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (hD : ∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0)
    (hI : ∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1)
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (hY : ∀ r, GlobalTheory.KA.ShCoc (fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l))) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r))
    (hc : ∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : G ℚ Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) →
      Cg n (Y r (s * s') y 1) (Y r s y 1))
    (hO : ∀ r s y, Y r s y 1 ∈ c.O) (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l) (m : ℕ) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (l ^ m)) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m 0 (fun r s y => Y r s y 1 - (d₀ : Qbar l) *
        Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) ζ P o := by
  classical
  have hnz : ∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 ≠ 0 := by
    intro s hs h
    have := (ρ s).det_ne_zero
    rw [Matrix.det_fin_two, hD s hs, h] at this
    simp at this
  let ν : G ℚ Ω → (Qbar l)ˣ := fun s =>
    if h : (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 ≠ 0 then Units.mk0 _ h else 1
  have hν : ∀ s ∈ Dec (F := ℚ) A, (ν s : Qbar l) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 := by
    intro s hs
    simp only [ν, dif_pos (hnz s hs), Units.val_mk0]
  refine smoothed_pres A hA c ν (fun r s y => Y r s y 1) (fun r => ⟨hO r, fun s hs u _ x => ?_⟩)
    (fun r => GlobalTheory.LambdaValuationPowers.AllRoots.continuous_of_cg _ fun n => ?_) (fun s hs => ?_) d₀ hd₀ m ζ hζ
  · have := congrFun (hY r s u x) 1
    show Y r (s * u) x 1 = Y r s x 1 + (ν s : Qbar l) * Y r u (x * (cycMod ℚ Ω l r s)⁻¹) 1
    rw [this, hν s hs]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hD s hs]
  · obtain ⟨E0, hE⟩ := hc r n
    exact ⟨E0, fun s s' h => hE s s' 1 h⟩
  · exact Units.ext (by rw [hν s (Ine_le_Dec A hs), hI s hs, Units.val_one])

theorem exists_pres_smoothed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
  ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
    AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
  ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
    IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
    (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
    (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
    (∀ r s y, Y r s y 1 ∈ cf.O) →
  ∀ (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), 2 ≤ d₀ →
  ∃ (m₀ c₀' : ℕ), ∀ m, m₀ ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
    HTPresNuOfPolys A cf m c₀' (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) ζ P o := by
  intro l _ Ω _ _ _ ι e S A W g hN hS ε X pr N _ cw c d gm ψ₀ cf α _ _ _ hAdm _ j _ c₀ Y hZ hY hc hO d₀ hd₀ _
  refine ⟨0, 0, fun m _ ζ hζ => ?_⟩
  by_cases hcw : ∃ x, cw x ≠ 0
  · obtain ⟨x, hx⟩ := hcw
    obtain ⟨ρ, hρ, -, hD, hI, -⟩ := GlobalTheory.RhoAdm.rho_ordinary_shape l Ω ι e S A W g ψ₀ hN hS
      (hAdm.1 x hx).2.2.2.2.2.2.2.2.2.2.2
    have hfun : rhoK W e ψ₀ = fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := funext fun s => (hρ s).symm
    exact smoothed_pres_of_shCoc A hN.atL cf ρ hD hI Y (fun r => hfun ▸ hY r) hc hO d₀ hd₀ m ζ hζ
  · refine GlobalTheory.LambdaValuationPowers.AllRoots.pres_of_vanish A cf _ m ζ hζ fun s _ _ => ?_
    obtain ⟨Yx, -, hs⟩ := hZ
    push_neg at hcw
    simp [hs, hcw]

end GlobalTheory.LambdaValuationPowers.Smooth
end
end
