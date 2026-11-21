import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingIntO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartExtensionHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameMoveHolds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsUniqueH0Section
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange

section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.LocM.FJ

section Directions

variable {L L' : Type} [AddCommGroup L] [AddCommGroup L'] {K : Type} [NormedField K]

def Nonneg (P : Set L) (χ : Module.Dual ℤ L) : Prop := ∀ γ ∈ P, 0 ≤ χ γ

def Isolates (P : Set L) (γ : L) (χ : Module.Dual ℤ L) : Prop :=
  γ ∈ P ∧ Nonneg P χ ∧ ∀ χ', Nonneg P χ' → χ' γ = χ γ → χ' = χ

def IsFat (P : Set L) : Prop := ∃ k : ℕ, 0 < k ∧ ∀ γ ∈ P, ∀ δ : L, ∃ C : ℕ, ∀ N : ℕ, C ≤ N → N • γ + k • δ ∈ P

def IsExpansion (P : Set L) (Val : L → LaurentSeries K → Prop) (c : Module.Dual ℤ L → K) : Prop :=
  (∀ χ, c χ ≠ 0 → Nonneg P χ) ∧
    ∀ γ ∈ P, ∀ r, Val γ r → ∀ n : ℤ, r.coeff n = ∑ᶠ (χ : Module.Dual ℤ L) (_ : χ γ = n), c χ

def coefSet (P : Set L) (Val : L → LaurentSeries K → Prop) (χ : Module.Dual ℤ L) : Set ℝ :=
  {x | ∃ γ r, Isolates P γ χ ∧ Val γ r ∧ x = ‖r.coeff (χ γ)‖}

def coefNorm (P : Set L) (Val : L → LaurentSeries K → Prop) (χ : Module.Dual ℤ L) : ℝ := sSup (coefSet P Val χ)

variable {P : Set L} {Val : L → LaurentSeries K → Prop} {χ : Module.Dual ℤ L}

theorem IsFat.bound {k : ℕ} (h : ∀ γ ∈ P, ∀ δ : L, ∃ C : ℕ, ∀ N : ℕ, C ≤ N → N • γ + k • δ ∈ P) {γ : L} (hγ : γ ∈ P)
    (δ : L) : ∃ C : ℕ, (∀ N : ℕ, C ≤ N → N • γ + k • δ ∈ P) ∧ ∀ χ, Nonneg P χ → |k * χ δ| ≤ C * χ γ := by
  obtain ⟨C₁, h₁⟩ := h γ hγ δ
  obtain ⟨C₂, h₂⟩ := h γ hγ (-δ)
  refine ⟨max C₁ C₂, fun N hN => h₁ N ((le_max_left _ _).trans hN), fun χ hχ => ?_⟩
  have a := hχ _ (h₁ _ (le_max_left C₁ C₂))
  have b := hχ _ (h₂ _ (le_max_right C₁ C₂))
  simp only [map_add, map_nsmul, map_neg, nsmul_eq_mul, mul_neg] at a b
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem IsFat.finite [Module.Finite ℤ L] (h : IsFat P) {γ : L} (hγ : γ ∈ P) (n : ℤ) :
    {χ : Module.Dual ℤ L | Nonneg P χ ∧ χ γ = n}.Finite := by
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨m, v, hv⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  choose C _ hC using fun i => IsFat.bound h hγ (v i)
  refine Set.Finite.of_finite_image (f := fun χ i => χ (v i))
    ((Set.Finite.pi' fun i => Set.finite_Icc (-(C i * n)) (C i * n)).subset ?_)
    fun χ _ χ' _ e => LinearMap.ext_on_range hv (congrFun e)
  rintro _ ⟨χ, ⟨h₁, rfl⟩, rfl⟩ i
  refine abs_le.1 (le_trans ?_ (hC i χ h₁))
  rw [abs_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) (by rw [Nat.abs_cast]; exact_mod_cast hk)

theorem exists_forall_ne_zero {T : Set (Module.Dual ℤ L)} (hT : T.Finite) (h : ∀ φ ∈ T, φ ≠ 0) :
    ∃ δ : L, ∀ φ ∈ T, φ δ ≠ 0 := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert φ T _ hT ih =>
    obtain ⟨δ, hδ⟩ := ih fun ψ hψ => h ψ (Set.mem_insert_of_mem _ hψ)
    obtain ⟨a, ha⟩ : ∃ a, φ a ≠ 0 := by
      by_contra! hh
      exact h φ (Set.mem_insert _ _) (LinearMap.ext hh)
    have fin : (⋃ ψ ∈ insert φ T, {n : ℤ | ψ (n • δ + a) = 0}).Finite := by
      refine (hT.insert φ).biUnion fun ψ hψ => Set.Subsingleton.finite fun n hn n' hn' => ?_
      simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul] at hn hn'
      by_cases h0 : ψ δ = 0
      · rcases hψ with rfl | hψ
        · rw [h0] at hn; exact absurd (by simpa using hn) ha
        · exact absurd h0 (hδ ψ hψ)
      · exact mul_right_cancel₀ h0 (by linarith)
    obtain ⟨n, hn⟩ := fin.exists_notMem
    exact ⟨n • δ + a, fun ψ hψ e => hn (Set.mem_biUnion hψ e)⟩

theorem IsFat.exists_isolates [Module.Finite ℤ L] (h : IsFat P) (hne : P.Nonempty) (hχ : Nonneg P χ) :
    ∃ γ, Isolates P γ χ := by
  obtain ⟨γ, hγ⟩ := hne
  have fin := h.finite hγ (χ γ)
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨δ, hδ⟩ := exists_forall_ne_zero (T := (fun χ' => χ' - χ) '' ({χ' | Nonneg P χ' ∧ χ' γ = χ γ} \ {χ}))
    ((fin.subset Set.diff_subset).image _) (by rintro _ ⟨χ', h', rfl⟩; exact sub_ne_zero.2 h'.2)
  obtain ⟨C, hC, hb⟩ := IsFat.bound h hγ δ
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (hχ γ hγ)
  refine ⟨_, hC (C * (2 * a + 1) + 1) (by nlinarith), hχ, fun χ' h' e => ?_⟩
  simp only [map_add, map_nsmul, nsmul_eq_mul] at e
  push_cast at e
  have b := abs_le.1 (hb χ hχ)
  have b' := abs_le.1 (hb χ' h')
  have n' := h' γ hγ
  have hC0 : (0 : ℤ) ≤ C := Int.natCast_nonneg _
  have ha0 : (0 : ℤ) ≤ a := Int.natCast_nonneg _
  have e₁ : χ' γ = χ γ := by
    rw [ha] at b e ⊢
    rcases lt_trichotomy (χ' γ) a with hl | hl | hl
    · nlinarith [mul_nonneg hC0 ha0, mul_nonneg (mul_nonneg hC0 ha0) (sub_nonneg.2 (Int.add_one_le_of_lt hl)),
        mul_nonneg hC0 (sub_nonneg.2 hl.le)]
    · exact hl
    · nlinarith [mul_nonneg (mul_nonneg hC0 ha0) (sub_nonneg.2 (Int.add_one_le_of_lt hl))]
  by_contra hne
  refine hδ _ ⟨χ', ⟨⟨h', e₁⟩, hne⟩, rfl⟩ ?_
  rw [e₁, add_right_inj] at e
  exact sub_eq_zero.2 (mul_left_cancel₀ (by exact_mod_cast hk.ne') e)

theorem IsExpansion.coeff_eq {c : Module.Dual ℤ L → K} (h : IsExpansion P Val c) {γ : L} (hγ : Isolates P γ χ)
    {r : LaurentSeries K} (hr : Val γ r) : r.coeff (χ γ) = c χ := by
  rw [h.2 γ hγ.1 r hr, finsum_eq_single _ χ]
  · exact finsum_eq_single (fun _ : χ γ = χ γ => c χ) rfl fun _ h => (h rfl).elim
  · intro χ' hne
    by_cases e : χ' γ = χ γ
    · simp [of_not_not fun h0 => hne (hγ.2.2 χ' (h.1 χ' h0) e)]
    · simp [e]

theorem coefNorm_eq_zero (h : ¬ Nonneg P χ) : coefNorm P Val χ = 0 := by
  rw [coefNorm, show coefSet P Val χ = ∅ from Set.eq_empty_of_forall_notMem fun _ ⟨_, _, h', _⟩ => h h'.2.1,
    Real.sSup_empty]

theorem coefSet_nonempty [Module.Finite ℤ L] (h : IsFat P) (hne : P.Nonempty) (hV : ∀ γ ∈ P, ∃ r, Val γ r)
    (hχ : Nonneg P χ) : (coefSet P Val χ).Nonempty := by
  obtain ⟨γ, hγ⟩ := h.exists_isolates hne hχ
  obtain ⟨r, hr⟩ := hV γ hγ.1
  exact ⟨_, γ, r, hγ, hr, rfl⟩

theorem IsExpansion.coefNorm_eq [Module.Finite ℤ L] {c : Module.Dual ℤ L → K} (hc : IsExpansion P Val c) (h : IsFat P)
    (hne : P.Nonempty) (hV : ∀ γ ∈ P, ∃ r, Val γ r) (χ : Module.Dual ℤ L) : coefNorm P Val χ = ‖c χ‖ := by
  by_cases hχ : Nonneg P χ
  · have : coefSet P Val χ = {‖c χ‖} := (coefSet_nonempty h hne hV hχ).subset_singleton_iff.1 (by
      rintro _ ⟨γ, r, hγ, hr, rfl⟩
      exact congrArg _ (hc.coeff_eq hγ hr))
    rw [coefNorm, this, csSup_singleton]
  · rw [coefNorm_eq_zero hχ, of_not_not fun h0 => hχ (hc.1 χ h0), norm_zero]

theorem IsExpansion.unique [Module.Finite ℤ L] {c c' : Module.Dual ℤ L → K} (hc : IsExpansion P Val c)
    (hc' : IsExpansion P Val c') (h : IsFat P) (hne : P.Nonempty) (hV : ∀ γ ∈ P, ∃ r, Val γ r) : c = c' := by
  funext χ
  by_cases hχ : Nonneg P χ
  · obtain ⟨γ, hγ⟩ := h.exists_isolates hne hχ
    obtain ⟨r, hr⟩ := hV γ hγ.1
    exact (hc.coeff_eq hγ hr).symm.trans (hc'.coeff_eq hγ hr)
  · rw [of_not_not fun h0 => hχ (hc.1 χ h0), of_not_not fun h0 => hχ (hc'.1 χ h0)]




theorem isFat_pos : IsFat {n : ℤ | 0 < n} := ⟨1, one_pos, fun γ hγ δ => ⟨δ.natAbs + 1, fun N hN => by
  have h : (0 : ℤ) < γ := hγ
  have hN' : |δ| + 1 ≤ (N : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hN
  change (0 : ℤ) < N • γ + 1 • δ
  rw [nsmul_eq_mul, one_smul]
  nlinarith [neg_abs_le δ, abs_nonneg δ]⟩⟩

theorem isExpansion_single [DecidableEq (Module.Dual ℤ L)] {χ₀ : Module.Dual ℤ L} (h : Nonneg P χ₀) (a : K) :
    IsExpansion P (fun γ r => r = HahnSeries.single (χ₀ γ) a) (fun χ => if χ = χ₀ then a else 0) := by
  refine ⟨fun χ hχ => (of_not_not fun e => hχ (if_neg e) : χ = χ₀) ▸ h, ?_⟩
  rintro γ - _ rfl n
  rw [finsum_eq_single _ χ₀ fun χ e => by simp [e]]
  simp only [if_true]
  by_cases e : χ₀ γ = n
  · subst e
    rw [HahnSeries.coeff_single_same]
    exact (finsum_eq_single (fun _ : χ₀ γ = χ₀ γ => a) rfl fun _ h => (h rfl).elim).symm
  · rw [HahnSeries.coeff_single_of_ne (Ne.symm e)]
    simp [e]

end Directions

section Forms

variable {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

theorem exists_sq_le {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y) (hp : ∀ y, y ≠ 0 → 0 < β y y)
    (φ : Module.Dual ℤ X) : ∃ C : ℕ, ∀ y, φ y ^ 2 ≤ C * β y y := by
  have nn : ∀ y, 0 ≤ β y y := fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (hp y h).le
  have inj : Function.Injective β := (injective_iff_map_eq_zero _).2 fun y hy => by
    by_contra h
    simpa [hy] using hp y h
  have tor : Module.IsTorsion ℤ (Module.Dual ℤ X ⧸ LinearMap.range β) := by
    rw [← Module.finrank_eq_zero_iff_isTorsion]
    have h₁ := Submodule.finrank_quotient_add_finrank (LinearMap.range β)
    rw [LinearMap.finrank_range_of_inj inj, Module.finrank_linearMap_self] at h₁
    exact Nat.add_eq_right.1 h₁
  obtain ⟨⟨d, hd⟩, h⟩ := @tor (Submodule.Quotient.mk φ)
  obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).1 (show Submodule.Quotient.mk (d • φ) = 0 from h)
  have hd1 : 1 ≤ d ^ 2 := (one_le_sq_iff_one_le_abs d).2 (Int.one_le_abs (nonZeroDivisors.ne_zero hd))
  obtain ⟨C, hC⟩ := Int.eq_ofNat_of_zero_le (nn z)
  refine ⟨C, fun y => ?_⟩
  have e : β z y = d * φ y := by rw [hz]; rfl
  have cs : β z y ^ 2 ≤ β z z * β y y := by
    by_cases h0 : z = 0
    · simp [h0]
    · have := nn (β z z • y - β z y • z)
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hs y z] at this
      exact le_of_mul_le_mul_left (by nlinarith) (hp z h0)
  rw [← hC]
  rw [e, mul_pow] at cs
  nlinarith [sq_nonneg (φ y)]

theorem exists_abs_le {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y) (hp : ∀ y, y ≠ 0 → 0 < β y y)
    (δ : LinearMap.BilinForm ℤ X) : ∃ C : ℕ, ∀ y, |δ y y| ≤ C * β y y := by
  let b := Module.finBasis ℤ X
  choose C hC using fun i => exists_sq_le hs hp (b.coord i)
  choose C' hC' using fun i => exists_sq_le hs hp (δ (b i))
  refine ⟨∑ i, (C i + C' i), fun y => ?_⟩
  have e : δ y y = ∑ i, b.coord i y * δ (b i) y := by
    refine (congrArg (fun z => δ z y) (b.sum_repr y).symm).trans ?_
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
  rw [e, Nat.cast_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h₁ := hC i y
  have h₂ := hC' i y
  push_cast
  refine abs_le.2 ⟨?_, ?_⟩ <;>
    nlinarith [sq_nonneg (b.coord i y + δ (b i) y), sq_nonneg (b.coord i y - δ (b i) y), sq_nonneg (b.coord i y),
      sq_nonneg (δ (b i) y)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (N : ℕ)

def admitted (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Set (levelForms H N X) :=
  {γ | (∀ y, y ≠ 0 → 0 < (γ : LinearMap.BilinForm ℤ X) y y) ∧ ∀ y z, (2 * N : ℤ) ∣ (γ : LinearMap.BilinForm ℤ X) y z}

variable [Module (𝓞 E) X]

variable (X) in

theorem isFat_adm : IsFat (admitted H N X) := by
  refine ⟨2, two_pos, fun γ hγ δ => ?_⟩
  obtain ⟨C, hC⟩ := exists_abs_le γ.2.1 hγ.1 δ.1
  refine ⟨2 * C + 1, fun n hn => ⟨fun y hy => ?_, fun y z => ?_⟩⟩
  · have h₁ := hγ.1 y hy
    have h₂ := (abs_le.1 (hC y)).1
    have h₃ : (2 * C + 1 : ℤ) ≤ n := by exact_mod_cast hn
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    push_cast
    nlinarith
  · simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_add ((hγ.2 y z).mul_left _) (mul_dvd_mul_left _ (δ.2.2.2 y z))

variable {H N} in
omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem nonneg_admissible_iff_positiveDefinite (χ : Module.Dual ℤ (levelForms H N X)) : Nonneg (admitted H N X) χ ↔
    ∀ γ : levelForms H N X, (∀ y, y ≠ 0 → 0 < (γ : LinearMap.BilinForm ℤ X) y y) → 0 ≤ χ γ := by
  refine ⟨fun h γ hγ => ?_, fun h γ hγ => h γ hγ.1⟩
  have := h ((2 : ℤ) • γ) ⟨fun y hy => mul_pos two_pos (hγ y hy), fun y z => mul_dvd_mul_left _ (γ.2.2.2 y z)⟩
  rw [map_smul, smul_eq_mul] at this
  omega

end Forms

end GlobalTheory.LocM.FJ
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.Points
open GlobalTheory.GradedPieces IsLocalRing

namespace GlobalTheory.LocM.FJ

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Value

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure GrTriv (Z : Mdl Y i₀) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) (F : Z.X.Modules) : Type 1 where

  L : LB Z.X

  isLB : L.IsLB

  hU : ∀ i, IsAffineOpen (L.U i)

  w : ∀ i, Vecs Dw (Y Z.i).t Γ(Z.X, L.U i)

  int : ∀ i, IntFrame Z (hU i) (w i)

  trans : ∀ (i i' : L.ι) (k : Type) [Field k] (φ : Γ(Z.X, L.U i) →+* k) (φ' : Γ(Z.X, L.U i') →+* k)
    (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    spMap φ ≫ (hU i).fromSpec = spMap φ' ≫ (hU i').fromSpec → Set.range (spMap φ ≫ (hU i).fromSpec) ⊆ Z.opn →
    (∀ σ, DiagAt (Y Z.i).t (spMap φ ≫ (hU i).fromSpec ≫ Z.π) ((w i').bc φ' σ) ((w i).bc φ σ) (d σ)) →
    valR (spMap φ ≫ (hU i).fromSpec) _ (L.g i i').val = ∏ σ, ∏ a, d σ a ^ e σ a

  iso : F ≅ GlobalTheory.LB.toMod L

variable {Z : Mdl Y i₀} {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ}

theorem nonempty_grTriv (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) {L : LB Z.X} (h : IsGrLB Z e L) :
    Nonempty (GrTriv Z e (Z.ofMod (GlobalTheory.LB.toMod L)).toMod) := by
  obtain ⟨hL, hU, w, hw, ht⟩ := h
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod L) := (GlobalTheory.VB.isVB_toMod hL).isFiniteQC
  obtain ⟨i⟩ := GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso E H Dw Xo p W hp hW Y i₀ Z (GlobalTheory.LB.toMod L)
  exact ⟨⟨L, hL, hU, w, hw, ht, i⟩⟩

variable {F : Z.X.Modules} (T : GrTriv Z e F) {V : Z.X.Opens} {k : Type} [Field k]

def GrTriv.IsVal (f : Γ(F, V)) (x : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) (r : k) : Prop :=
  ⊤ ≤ x ⁻¹ᵁ V ∧ ∃ (i : T.L.ι) (φ : Γ(Z.X, T.L.U i) →+* k) (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    spMap φ ≫ (T.hU i).fromSpec = x ∧ (∀ σ, DiagAt (Y Z.i).t (x ≫ Z.π) ((T.w i).bc φ σ) (u σ) (d σ)) ∧
    r = valR x (V ⊓ T.L.U i) (GlobalTheory.LB.coord (T.iso.hom.app V f) i) * ∏ σ, ∏ a, d σ a ^ e σ a

theorem range_subset_opn {x : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u) : Set.range x ⊆ Z.opn := by
  obtain ⟨a, φ, rfl, -⟩ := h
  rintro _ ⟨z, rfl⟩
  rw [← Z.cover]
  exact Set.mem_iUnion.2 ⟨a, le_preimage_specMap_fromSpec (Z.U a).2 (CommRingCat.ofHom φ) (Set.mem_univ z)⟩

theorem GrTriv.existsUnique_isVal (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) (f : Γ(F, V)) {x : Sp k ⟶ Z.X}
    (hx : ⊤ ≤ x ⁻¹ᵁ V) {u : Vecs Dw (Y Z.i).t k} (hu : Z.FlagAt x u) : ∃! r, T.IsVal f x u r := by
  have ho := range_subset_opn hu
  have tu : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u σ i) := fun σ i => by
    obtain ⟨_, _, -, h, -⟩ := hu
    exact (h.1 σ i).1
  have fl : ∀ i (φ : Γ(Z.X, T.L.U i) →+* k), spMap φ ≫ (T.hU i).fromSpec = x → Z.FlagAt x ((T.w i).bc φ) :=
    fun i φ h => h ▸ (T.int i).2 k φ (h ▸ ho)
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (T.isLB.cover.ge (Set.mem_univ (x (closedPoint k))))
    have h : ⊤ ≤ x ⁻¹ᵁ T.L.U i := fun z _ => by
      obtain rfl : z = closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
      exact hi
    have e₁ := specMap_valMap_fromSpec (T.hU i) x h
    choose d hd using fun σ => exists_diag_of_flagAt Z hty hu (fl i _ e₁) σ (tu σ) (tan_bc (T.int i) _ e₁ σ)
      (linInd_bc (T.int i) _ e₁ σ)
    exact ⟨_, hx, i, _, d, e₁, fun σ => (diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu σ) (d σ)).2 (hd σ), rfl⟩
  · rintro _ _ ⟨-, i, φ, d, e₁, hd, rfl⟩ ⟨-, i', φ', d', e₂, hd', rfl⟩
    choose D hD using fun σ => exists_diag_of_flagAt Z hty (fl i _ e₁) (fl i' _ e₂) σ (tan_bc (T.int i) _ e₁ σ)
      (tan_bc (T.int i') _ e₂ σ) (linInd_bc (T.int i') _ e₂ σ)
    have hg := T.trans i i' k φ φ' D (e₁.trans e₂.symm) (e₁ ▸ ho) fun σ => by
      rw [← Category.assoc, e₁]
      exact (diagAt_iff (tan_bc (T.int i') _ e₂ σ) (tan_bc (T.int i) _ e₁ σ) (D σ)).2 (hD σ)
    have hd'' : ∀ σ, d' σ = fun a => d σ a * D σ a := fun σ =>
      ((diagAt_iff (tan_bc (T.int i') _ e₂ σ) (tu σ) _).1 (hd' σ)).unique (linInd_bc (T.int i') _ e₂ σ)
        ((hD σ).trans ((diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu σ) _).1 (hd σ)))
    have h₁ : ⊤ ≤ x ⁻¹ᵁ T.L.U i := e₁ ▸ le_preimage_specMap_fromSpec (T.hU i) (CommRingCat.ofHom φ)
    have h₂ : ⊤ ≤ x ⁻¹ᵁ T.L.U i' := e₂ ▸ le_preimage_specMap_fromSpec (T.hU i') (CommRingCat.ofHom φ')
    have h₃ : ⊤ ≤ x ⁻¹ᵁ (V ⊓ T.L.U i ⊓ T.L.U i') := fun z hz => ⟨⟨hx hz, h₁ hz⟩, h₂ hz⟩
    have hc := congrArg (valR x _) (GlobalTheory.LB.coord_mem (T.iso.hom.app V f) i i')
    rw [valR_mul x _ h₃] at hc
    erw [valR_res x _ h₃, valR_res x _ h₃, valR_res x _ h₃] at hc
    rw [e₁] at hg
    rw [hc, hg]
    simp only [hd'', mul_zpow, Finset.prod_mul_distrib]
    ring

theorem GrTriv.IsVal.change {T : GrTriv Z e F} {f : Γ(F, V)} {x : Sp k ⟶ Z.X} {u u' : Vecs Dw (Y Z.i).t k} {r : k}
    (h : T.IsVal f x u r) (tu : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u σ i))
    (tu' : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u' σ i)) {d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k}
    (hd : ∀ σ, DiagAt (Y Z.i).t (x ≫ Z.π) (u σ) (u' σ) (d σ)) : T.IsVal f x u' (r * ∏ σ, ∏ a, d σ a ^ e σ a) := by
  obtain ⟨hx, i, φ, D, e₁, hD, rfl⟩ := h
  refine ⟨hx, i, φ, fun σ a => d σ a * D σ a, e₁, fun σ => (diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu' σ) _).2
    (((diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu σ) _).1 (hD σ)).trans ((diagAt_iff (tu σ) (tu' σ) _).1 (hd σ))), ?_⟩
  simp only [mul_zpow, Finset.prod_mul_distrib]
  ring


end Value

end GlobalTheory.LocM.FJ
end
end

section
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.ArcQ (Wit LieImg ArcBasis)
open GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints (EpsPt IsLetters)

namespace GlobalTheory.LocM.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

structure DVF (p : ℕ) : Type where

  C : SCF p

  K : Subfield ↥C.S

  closed : IsClosed (K : Set ↥C.S)

  dvr : IsDiscreteValuationRing ↥(intO ↥K)

namespace DVF

variable {p : ℕ} (F : DVF p)

abbrev O : Type := ↥(intO ↥F.K)

instance : IsDiscreteValuationRing F.O := F.dvr

def toLaurent : PowerSeries F.O →+* LaurentSeries ↥F.K :=
  (HahnSeries.ofPowerSeries ℤ ↥F.K).comp (PowerSeries.map (intO ↥F.K).subtype)

theorem toLaurent_injective : Function.Injective F.toLaurent :=
  fun _ _ h => PowerSeries.map_injective (intO ↥F.K).subtype Subtype.val_injective
    (HahnSeries.ofPowerSeries_injective (Γ := ℤ) h)


theorem isAdicComplete {ϖ : F.O} (h : Irreducible ϖ) : IsAdicComplete (Ideal.span {ϖ}) F.O := by
  haveI : CompleteSpace ↥F.K := F.closed.completeSpace_coe
  have hO : (NormedField.valuation (K := ↥F.K)).Integers F.O :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_coe]
        exact x.2
      exists_of_le_one := fun r hr => ⟨⟨r, by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_coe] at hr
        exact hr⟩, rfl⟩ }
  exact NormIntegers.isAdicComplete_span_singleton hO
    ((Cht.mem_maximalIdeal_ball ϖ).1 ((mem_maximalIdeal _).2 h.not_isUnit))

end DVF


section Cusp

variable {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {A : Type} [CommRing A] [IsDomain A]

@[reducible] def withForm {b : O →+* A} (a : ArcIn Dw l β A b) (γ : levelForms H l.M' a.D₀.X)
    (h : γ ∈ admitted H l.M' a.D₀.X) : ArcIn Dw l β A b :=
  { a with be := γ.1, be_symm := γ.2.1, be_pos := h.1, be_adj := γ.2.2.1, be_dvd := h.2 }

variable (Dw l β A) in

structure Cusp : Type 1 where

  b : O →+* A

  a : ArcIn Dw l β A b

  e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → EpsPt a.D₀

  letters : ∃ io : c.F →+* FractionRing A, IsLetters a io e

namespace Cusp

variable (t : Cusp Dw l β A)

abbrev Forms : Type := levelForms H l.M' t.a.D₀.X

abbrev Chr : Type := Module.Dual ℤ t.Forms

abbrev Dir : Set t.Forms := admitted H l.M' t.a.D₀.X

theorem dir_nonempty : t.Dir.Nonempty :=
  ⟨⟨t.a.be, t.a.be_symm, t.a.be_adj, fun y z => (dvd_mul_left _ _).trans (t.a.be_dvd y z)⟩, t.a.be_pos, t.a.be_dvd⟩

theorem isFat_dir : IsFat t.Dir := isFat_adm _ H l.M'


end Cusp

section Toric

open GlobalTheory.HostModel GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out

def fracRoot (io : c.F →+* FractionRing A) {n : ℕ} (h : n ∣ l.M') : (FractionRing A)ˣ :=
  Units.map io.toMonoidHom
    (Units.mk0 ⟨zeta n, zeta_mem_coeff_of_dvd c h⟩ fun e => Complex.exp_ne_zero _ (congrArg Subtype.val e))

theorem fracRoot_pow (io : c.F →+* FractionRing A) {n : ℕ} (h : n ∣ l.M') : fracRoot io h ^ n = 1 := by
  rw [fracRoot, ← map_pow, ← map_one (Units.map io.toMonoidHom)]
  exact congrArg _ (Units.ext (Subtype.ext (isPrimitiveRoot_zeta (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l))).pow_eq_one))

def toricIn (b : O →+* A) (io : c.F →+* FractionRing A) (hio : io.comp β = (algebraMap A _).comp b) :
    ArcIn (hypDatum H) l β A b where
  D₀ := toricPre A (𝓞 E) fun _ => 1
  oa := arcAct H A
  nontriv := inferInstanceAs (Nontrivial (𝓞 E))
  even := psiEven _ fun _ => rfl
  bimult := tauBimult _ fun _ _ _ => by simp [polar_one]
  gen y := psiUnitOn _ y 1 (by simp)
  w0 := letI := H.starRing; psi_weight_zero_linear_combination _ (𝓞 E) (polar_one_smul A) H.w0 fun _ => polar_one A _ _
  be := arcForm l
  be_symm (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z)
  be_pos (y : 𝓞 E) hy := mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy)
  be_adj a (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_adj H a y z)
  be_dvd (y z : 𝓞 E) := ⟨trForm H y z, rfl⟩
  eta := qkPt A (fracRoot io (Nat.dvd_lcm_left l.M l.A)) (fracRoot_pow io _)
  etaA := qkPt A (fracRoot io (Nat.dvd_lcm_right l.M l.A)) (fracRoot_pow io _)
  geom := by
    letI := H.starRing
    intro F _ _ _ r z _ hz f hf
    refine ⟨fun τ => ⟨0, lieMult_zero _ (𝓞 E) (polar_one_smul A) f τ, ?_⟩, ?_⟩
    · rw [hypDatum_p, hypDatum_q, ite_self, zero_add]
      exact Module.finrank_self (𝓞 E)
    haveI := c.fin
    obtain ⟨ζ, hp, hc, hζ⟩ := exists_roots c.F F ((algebraMap (FractionRing A) F).comp io)
    have key : ∀ {n : ℕ} (h : n ∣ l.M') (a : HypLattice H) q,
        QkExt (algebraMap _ F) (qkPt A (fracRoot io h) (fracRoot_pow io h) a) q →
          QkPt.Equiv _ F q ((tateIsoQ H A ζ hp hc).ev n a) := fun {n} h a q hq => by
      rw [qkExt_qkPt A _ (algebraMap (FractionRing A) F) (RingHom.ext fun _ => rfl) (pow_eq_one_of_prim hp n)
        (hζ n (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l)) ⟨zeta n, zeta_mem_coeff_of_dvd c h⟩ rfl)] at hq
      subst hq
      exact equiv_refl_split A F _
    exact ⟨tateIsoQ H A ζ hp hc, (hζ l.A l.A_pos (β z) hz).trans
      (by rw [hf]; exact congrArg (algebraMap (FractionRing A) F) (RingHom.congr_fun hio z)), key _, fun a _ => key _ a⟩

end Toric

variable {p : ℕ} {W : ValuationSubring ℂ} {F : DVF p}

theorem exists_io {K : Type} [Field K] {V : ValuationSubring K} {b : V →+* A} (hb : Function.Injective b) :
    ∃ io : K →+* FractionRing A, io.comp V.subtype = (algebraMap A (FractionRing A)).comp b := by
  have h : Function.Injective ((algebraMap A (FractionRing A)).comp b) :=
    fun x y e => hb (IsFractionRing.injective A (FractionRing A) e)
  refine ⟨IsFractionRing.lift (A := V) (K := K) h, RingHom.ext fun x => ?_⟩
  exact IsFractionRing.lift_algebraMap (A := V) (K := K) h x

theorem exists_chart {Xo : Moduli Dw l} {Y : Model Xo c (c.V W).subtype} (hY : Y.N4) {b : c.V W →+* F.O}
    (a : ArcIn Dw l (c.V W).subtype F.O b) :
    ∃ (ϖ : F.O) (χ : Sp (PowerSeries F.O) ⟶ Y.X), Irreducible ϖ ∧ IsArcChart Y a ϖ χ ∧ Nonempty (Wit Y a χ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible F.O
  obtain ⟨χ, hχ, -⟩ := hY F.O b ϖ a (Or.inr ⟨inferInstance, hϖ, F.isAdicComplete hϖ⟩)
  exact ⟨ϖ, χ, hϖ, (hχ χ).1 rfl, (Y.hasArcData_iff _ _ _ _ _).1 ((hχ χ).1 rfl).2.2.2⟩

theorem exists_cusp {Xo : Moduli Dw l} {Y : Model Xo c (c.V W).subtype} (hY : Y.N4) {b : c.V W →+* F.O}
    (hb : Function.Injective b) (a : ArcIn Dw l (c.V W).subtype F.O b) :
    ∃ t : Cusp Dw l (c.V W).subtype F.O, t.b = b ∧ HEq t.a a := by
  obtain ⟨io, hio⟩ := exists_io hb
  obtain ⟨ϖ, χ, -, -, ⟨Wt⟩⟩ := exists_chart hY a
  have hρ : ∀ τ x, algebraMap F.O (FractionRing F.O) (b.comp (IntModelExists.embV c W τ) x) = io (embK c τ x) :=
    fun τ x => (RingHom.congr_fun hio (IntModelExists.embV c W τ x)).symm
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_constant_eigenbasis_tangent_arc abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H Dw l Xo c _ _ Y F.O b a χ Wt
    (fun τ => b.comp (IntModelExists.embV c W τ)) io hio hρ (IntModelExists.exists_values c W)
  exact ⟨⟨b, a, e, io, (ArcCompare.isLetters_iff Wt io e).2 ⟨hio, _, fun τ => RingHom.ext (hρ τ), he⟩⟩, rfl, HEq.rfl⟩


end Cusp

section Bridge

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] (t : SAB H (Sp S))

theorem isTanAtG_id (v : epsR S ⟶ t.G) : IsTanAtG t (𝟙 _) v.left ↔ IsTangent v := by
  have e : (1 : Over.mk (𝟙 (Sp S)) ⟶ t.G).left = η[t.G].left := by
    rw [Hom.one_def, show toUnit (Over.mk (𝟙 (Sp S))) = 𝟙 (𝟙_ (Over (Sp S))) from toUnit_unique _ _]
    exact congrArg (·.left) (Category.id_comp η[t.G])
  exact ⟨fun h => h.2.trans e, fun h => ⟨(Over.w v).trans (Category.comp_id _).symm, Eq.trans h e.symm⟩⟩

theorem isCombAtG_id {n : ℕ} (v : Fin n → (epsR S ⟶ t.G)) (cf : Fin n → S) (w : epsR S ⟶ t.G) :
    IsCombAtG t (𝟙 _) (fun i => (v i).left) cf w.left ↔ IsLieComb cf v w := by
  have e := Category.comp_id (spMap (algebraMap S (DualNumber S)))
  constructor
  · rintro ⟨u, hu, h⟩
    refine ⟨fun i => Over.homMk (u i).left ((Over.w (u i)).trans e), hu, Over.OverMorphism.ext (h.symm.trans ?_)⟩
    exact BaseMdl.prod_left_congr e _ _ fun _ => rfl
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => Over.homMk (u i).left ((Over.w (u i)).trans e.symm), hu, ?_⟩
    exact BaseMdl.prod_left_congr e _ _ fun _ => rfl

theorem isFrame_id {l : Level H} {c : Coeff l} (g : c.F →+* S) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t.G))
    (h : ∀ τ, (∀ k, IsTangent (u τ k) ∧
        ∀ x : 𝓞 E, (u τ k ≫ t.act.act x).left = spMap (epsScaleR (g (embK c τ x))) ≫ (u τ k).left) ∧
      ∀ w : epsR S ⟶ t.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t.act.act x).left = spMap (epsScaleR (g (embK c τ x))) ≫ w.left) →
        ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w) :
    IsFrame (Dw := Dw) t g (𝟙 _) fun τ k => (u τ k).left := by
  refine ⟨fun τ k => ⟨(isTanAtG_id t _).2 ((h τ).1 k).1, ((h τ).1 k).2⟩, fun τ w hw he => ?_⟩
  let w' : epsR S ⟶ t.G := Over.homMk w (hw.1.trans (Category.comp_id _))
  exact (existsUnique_congr fun cf => isCombAtG_id t (u τ) cf w').2 ((h τ).2 w' ((isTanAtG_id t w').1 hw) he)

end Bridge

section Arcs

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

abbrev CuspOn (Z : Mdl Y i₀) (F : DVF p) : Type 1 := Cusp Dw Z.i.l (Z.i.c.V W).subtype F.O

variable {Z : Mdl Y i₀} {F : DVF p} (t : CuspOn Z F)

def IsArc (γ : t.Forms) (x : Sp (LaurentSeries ↥F.K) ⟶ Z.X) (v : Vecs Dw (Y Z.i).t (LaurentSeries ↥F.K)) : Prop :=
  ∃ (h : γ ∈ t.Dir) (ϖ : F.O) (χ : Sp (PowerSeries F.O) ⟶ (Y Z.i).X) (Wt : Wit (Y Z.i) (withForm t.a γ h) χ)
    (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries F.O) ⟶ Wt.t.G)),
    Irreducible ϖ ∧ IsArcChart (Y Z.i) (withForm t.a γ h) ϖ χ ∧ (∀ τ k, LieImg Wt (t.e τ k) (w τ k)) ∧
    x ≫ Z.π = spMap F.toLaurent ≫ χ ∧ (∀ τ k, v τ k = spMap (dualMap F.toLaurent) ≫ (w τ k).left ≫ Wt.m.φ) ∧ Z.FlagAt x v

variable {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ} {M : Z.X.Modules} (T : GrTriv Z e M) (f : Γ(M, Z.genO))

def IsSeries (γ : t.Forms) (r : LaurentSeries ↥F.K) : Prop := ∃ x v, IsArc t γ x v ∧ T.IsVal f x v r

def IsFJ (c : t.Chr → ↥F.K) : Prop := IsExpansion t.Dir (IsSeries t T f) c

def fjNorm (χ : t.Chr) : ℝ := coefNorm t.Dir (IsSeries t T f) χ

example (γ₀ : t.Forms) (h : γ₀ ∈ t.Dir) :
    fjNorm (Z := Z) ⟨t.b, withForm t.a γ₀ h, t.e, t.letters⟩ T f = fjNorm t T f := rfl

theorem le_preimage_genO (hp : p ≠ 0) {k : Type} [Field k] [CharZero k] (x : Sp k ⟶ Z.X) : ⊤ ≤ x ⁻¹ᵁ Z.genO := by
  rw [Mdl.genO, Scheme.preimage_basicOpen_top, map_natCast]
  refine (Scheme.basicOpen_of_isUnit _ ?_).ge
  have := (IsUnit.mk0 (p : k) (Nat.cast_ne_zero.2 hp)).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  rwa [map_natCast] at this

theorem exists_isArc (hY : (Y Z.i).N4) {γ : t.Forms} (h : γ ∈ t.Dir) : ∃ x v, IsArc t γ x v := by
  obtain ⟨ϖ, χ, hϖ, hχ, ⟨Wt⟩⟩ := exists_chart hY (withForm t.a γ h)
  obtain ⟨io, hio⟩ := t.letters
  obtain ⟨hb, ρ, hρ, he⟩ := (ArcCompare.isLetters_iff Wt io t.e).1 hio
  have inj := F.toLaurent_injective
  obtain ⟨g, y, hy, hyj⟩ := (Cht.extendSt E H Dw Xo p W Y i₀).1 Z.i _ (spMap F.toLaurent ≫ χ) (by
    rintro _ ⟨z, rfl⟩
    refine hχ.2.2.1 _ fun hz => mul_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hϖ.ne_zero)
      PowerSeries.X_ne_zero ((injective_iff_map_eq_zero _).1 inj _ ?_)
    have hz' : F.toLaurent (PowerSeries.C ϖ * PowerSeries.X) ∈ z.asIdeal := hz
    rwa [show z.asIdeal = ⊥ from @Ideal.eq_bot_of_prime _ _ _ z.2] at hz')
  let j : F.O →+* LaurentSeries ↥F.K := F.toLaurent.comp PowerSeries.C
  have hj : Function.Injective j := inj.comp PowerSeries.C_injective
  have hg : g.comp (Z.i.c.V W).subtype = j.comp t.b := by
    have e₁ : spMap (g.comp (Z.i.c.V W).subtype) = spMap (j.comp t.b) := by
      rw [spMap_comp, ← hy, Category.assoc, ← (Y Z.i).j_s, ← Category.assoc, hyj, Category.assoc, hχ.1, spMap_comp,
        spMap_comp, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e₁)
  have hv : ∀ τ a, g (embK Z.i.c τ a) = j (ρ τ a) := fun τ a => by
    have e₁ : ρ τ a = t.b (IntModelExists.embV Z.i.c W τ a) := IsFractionRing.injective F.O (FractionRing F.O)
      ((RingHom.congr_fun (hρ τ) a).trans (RingHom.congr_fun hb (IntModelExists.embV Z.i.c W τ a)))
    rw [e₁]
    exact RingHom.congr_fun hg (IntModelExists.embV Z.i.c W τ a)
  obtain ⟨t', ⟨m⟩⟩ := exists_sab (spMap F.toLaurent) Wt.t
  obtain ⟨u, hu, hbas⟩ := GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange globalFns_holds E H Dw _ _ _ _ _ (Y Z.i) F.O _ _ χ Wt ρ t.e he _ F.toLaurent
    (IntModelExists.flat_of_injective _ hj) t' m
  choose w hw hw' using hu
  have fr : IsFrame (Dw := Dw) t' g (𝟙 _) fun τ k => (u τ k).left := isFrame_id t' g u (by simpa only [hv] using hbas)
  have fr₁ := (Cht.frameMove E H Dw _ _ Z.i.c Z.i.c _ _ Wt.t t' _ m _ g g _ fun _ _ => rfl).1 _ fr
  have fr₂ := (Cht.frameMove E H Dw _ _ Z.i.c Z.i.c _ _ (Y Z.i).t Wt.t _ Wt.m _ g g _ fun _ _ => rfl).1 _ fr₁
  rw [Category.id_comp, ← hyj] at fr₂
  obtain ⟨x, ⟨hx, hfl⟩, -⟩ := Z.bij _ g y hy _ fr₂
  exact ⟨x, _, h, ϖ, χ, Wt, w, hϖ, hχ, hw, hx.trans hyj, fun τ k => by rw [hw', Category.assoc], hfl⟩

theorem exists_isSeries (hp : p ≠ 0) (hY : (Y Z.i).N4) (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {γ : t.Forms}
    (h : γ ∈ t.Dir) : ∃ r, IsSeries t T f γ r := by
  obtain ⟨x, v, hx⟩ := exists_isArc t hY h
  obtain ⟨_, _, _, _, _, -, -, -, -, -, hfl⟩ := id hx
  haveI : CharZero (LaurentSeries ↥F.K) := charZero_of_injective_ringHom (HahnSeries.C (Γ := ℤ) (R := ↥F.K)).injective
  obtain ⟨r, hr, -⟩ := T.existsUnique_isVal hty f (le_preimage_genO hp x) hfl
  exact ⟨r, x, v, hx, hr⟩

variable (Z) in

structure CuspRec : Type where

  F : DVF p

  m : ℕ

  dir : Set (Fin m → ℤ)

  arc : (Fin m → ℤ) → (Sp (LaurentSeries ↥F.K) ⟶ Z.X) → Vecs Dw (Y Z.i).t (LaurentSeries ↥F.K) → Prop

  ex : ∃ (t : CuspOn Z F) (ε : t.Forms ≃ₗ[ℤ] (Fin m → ℤ)), (∀ γ, ε γ ∈ dir ↔ γ ∈ t.Dir) ∧
    ∀ γ x v, arc (ε γ) x v ↔ IsArc t γ x v

def CuspRec.cusp (s : CuspRec Z) : CuspOn Z s.F := s.ex.choose

def CuspRec.of : CuspRec Z where
  F := F
  m := Module.finrank ℤ t.Forms
  dir := (Module.finBasis ℤ t.Forms).equivFun.symm ⁻¹' t.Dir
  arc γ := IsArc t ((Module.finBasis ℤ t.Forms).equivFun.symm γ)
  ex := ⟨t, (Module.finBasis ℤ t.Forms).equivFun, fun γ => by rw [Set.mem_preimage, LinearEquiv.symm_apply_apply],
    fun γ x v => by rw [LinearEquiv.symm_apply_apply]⟩

theorem CuspRec.exists_equiv : ∃ ε : (CuspRec.of t).cusp.Forms ≃ₗ[ℤ] t.Forms,
    (∀ γ, ε γ ∈ t.Dir ↔ γ ∈ (CuspRec.of t).cusp.Dir) ∧ ∀ γ x v, IsArc t (ε γ) x v ↔ IsArc (CuspRec.of t).cusp γ x v := by
  obtain ⟨ε, h₁, h₂⟩ := (CuspRec.of t).ex.choose_spec
  exact ⟨ε.trans (Module.finBasis ℤ t.Forms).equivFun.symm, h₁, h₂⟩


end Arcs

example {K : Type} [NormedField K] (a : K) :
    coefNorm {n : ℤ | 0 < n} (fun γ r => r = HahnSeries.single γ a) LinearMap.id = ‖a‖ ∧
      coefNorm {n : ℤ | 0 < n} (fun γ r => r = HahnSeries.single γ a) (2 • LinearMap.id) = 0 := by
  classical
  have h := (isExpansion_single (P := {n : ℤ | 0 < n}) (χ₀ := LinearMap.id) (fun _ h => le_of_lt h) a).coefNorm_eq
    isFat_pos ⟨1, show (0 : ℤ) < 1 from one_pos⟩ fun _ _ => ⟨_, rfl⟩
  refine ⟨(h _).trans (by simp), (h _).trans ?_⟩
  rw [if_neg fun e => by simpa using LinearMap.congr_fun e 1, norm_zero]

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

theorem nonempty_lbTriv (l : PsiT D → ℕ → ℤ) : Nonempty (GrTriv ct.YY (ct.expo l) (ct.Lb l).toMod) := by
  have h := GradedPieces.exists_isGrLB _ _ _ _ p ct.W ct.hp ct.hW _ _ ct.YY ct.isYY.2.1 (ct.expo l)
  unfold At.Lb
  rw [dif_pos h]
  exact nonempty_grTriv ct.hp ct.hW h.choose_spec

def lbTriv (l : PsiT D → ℕ → ℤ) : GrTriv ct.YY (ct.expo l) (ct.Lb l).toMod := (nonempty_lbTriv ct l).some

theorem charts_YY : (ct.Y ct.YY.i).N4 := ((S.sys.clauses p ct.W ct.hp ct.hW).2 _).2.2

end GlobalTheory.LocM.FJ

namespace GlobalTheory.LocM

open FJ

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def fjTrue (ct : At S κ p) : FJSt ct where
  FJd := CuspRec ct.YY
  Chr s := s.cusp.Chr
  fjN l f s χ := fjNorm s.cusp (lbTriv ct l) f χ

namespace FJ

variable {ct : At S κ p} {l : PsiT D → ℕ → ℤ} {f : ct.Sec (ct.Lb l)}



theorem IsFJ.unique {F : DVF p} {t : CuspOn ct.YY F} {c c' : t.Chr → ↥F.K} (h : IsFJ t (lbTriv ct l) f c)
    (h' : IsFJ t (lbTriv ct l) f c') : c = c' :=
  IsExpansion.unique h h' t.isFat_dir t.dir_nonempty fun _ => exists_isSeries t _ f ct.hp.ne_zero (charts_YY ct) ct.isYY.2.1.1






end FJ

end GlobalTheory.LocM
end
end
