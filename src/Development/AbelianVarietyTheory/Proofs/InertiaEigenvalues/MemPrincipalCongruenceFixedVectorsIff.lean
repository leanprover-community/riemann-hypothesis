import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionActionOnFixK1
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperMulInc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelOfParabolicVector

section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_unipotent_invariant : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Gn g n) W) (ρ' : Representation ℂ (Gn g n) W') (T : W →ₗ[ℂ] W') (a : Fin n → ℤ) (f f' : (ZMod g)[X]), (∀ u : Gn g n, (∀ i j, ¬ a i < a j → (u : Mt g n) i j = (1 : Mt g n) i j) → T ∘ₗ ρ u = T) → (∀ u : Gn g n, (∀ i j, ¬ a j < a i → (u : Mt g n) i j = (1 : Mt g n) i j) → ρ' u ∘ₗ T = T) → (∀ m : Gn g n, (∀ i j, a i ≠ a j → (m : Mt g n) i j = 0) → T ∘ₗ ρ m = ρ' m ∘ₗ T) → (∀ w, ρ.asAlgebraHom (eSerC L n f) w = w) → (∀ w', ρ'.asAlgebraHom (eSerC L n f') w' = w') → T ≠ 0 → f = f' := by
  first | exact @GlobalTheory.GLq.Opp.label_eq_of_opposite | exact GlobalTheory.GLq.Opp.label_eq_of_opposite | (intros; apply GlobalTheory.GLq.Opp.label_eq_of_opposite <;> assumption)
end

section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp

theorem cartan_decomposition (g : ℕ) [Fact g.Prime] (n : ℕ) (h : GL (Fin n) ℚ_[g]) :
    ∃ (k k' : GL (Fin n) ℤ_[g]) (a : Fin n → ℤ), Antitone a ∧ (h : Matrix (Fin n) (Fin n) ℚ_[g]) =
      (inc g n k : Matrix (Fin n) (Fin n) ℚ_[g]) * Matrix.diagonal (fun i => (g : ℚ_[g]) ^ a i) *
        (inc g n k' : Matrix (Fin n) (Fin n) ℚ_[g]) := by
  have hP : IsPrincipalIdealRing (PadicInt.subring g) :=
    inferInstanceAs (IsPrincipalIdealRing ℤ_[g])
  have hg0 : (g : ℚ_[g]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  obtain ⟨c, hc0, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ_[g])
    (fun ij : Fin n × Fin n => (h : Matrix (Fin n) (Fin n) ℚ_[g]) ij.1 ij.2) |>.imp
      (fun c hc => And.intro (nonZeroDivisors.coe_ne_zero c) hc)
  choose G hG using hc
  obtain ⟨a, ha, k₁, ⟨k, rfl⟩, k₂, ⟨k', rfl⟩, e⟩ :=
    Formalism.UG.P.cartan_decomp_gen (PadicInt.subring g) (NormedField.valuation (K := ℚ_[g]))
      (fun x => by
        rw [PadicInt.mem_subring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]; rfl)
      (g : ℚ_[g]) hg0
      (fun x hx => ⟨x.valuation, by
        apply NNReal.coe_injective
        rw [NormedField.valuation_apply, NormedField.valuation_apply, NNReal.coe_zpow, coe_nnnorm,
          coe_nnnorm, Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_p, inv_zpow']⟩)
      h (c : ℤ_[g]) hc0 ⟨Matrix.of fun i j => G (i, j), by
        ext i j
        exact hG (i, j)⟩
  exact ⟨k, k', a, ha, e⟩

end GlobalTheory.GLp
end

section
section
noncomputable section

namespace GlobalTheory.GLp.OneLabel

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

section Abstract

variable {K Γ U U' : Type} [Group K] [Group Γ] [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']

theorem exists_descend (r : K →* Γ) (hr : Function.Surjective r) (ρ : Representation ℂ K U)
    (h : ∀ s, r s = 1 → ∀ u, ρ s u = u) : ∃ σ : Representation ℂ Γ U, ∀ k, σ (r k) = ρ k := by
  have key : ∀ k k', r k = r k' → ρ k = ρ k' := by
    intro k k' e
    have h1 : k = k' * (k'⁻¹ * k) := by group
    ext u
    conv_lhs => rw [h1, map_mul, Module.End.mul_apply, h (k'⁻¹ * k) (by simp [e])]
  refine ⟨{ toFun := fun x => ρ (Function.surjInv hr x), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · rw [key _ 1 (by simp [Function.surjInv_eq]), map_one]
  · intro x y
    rw [← map_mul]
    exact key _ _ (by simp [Function.surjInv_eq])
  · intro k
    exact key _ _ (by simp [Function.surjInv_eq])

theorem map_asAlgebraHom (ρ : Representation ℂ Γ U) (ρ' : Representation ℂ Γ U') (φ : U →ₗ[ℂ] U')
    (h : ∀ x u, φ (ρ x u) = ρ' x (φ u)) (a : MonoidAlgebra ℂ Γ) (u : U) :
    φ (ρ.asAlgebraHom a u) = ρ'.asAlgebraHom a (φ u) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single x c => simp [h]

theorem asAlgebraHom_eq_sum [Fintype Γ] (ρ : Representation ℂ Γ U) (a : MonoidAlgebra ℂ Γ) :
    ρ.asAlgebraHom a = ∑ x, a.coeff x • ρ x := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single x c => simp [Finsupp.single_apply, ite_smul]

theorem central_comm (ρ : Representation ℂ Γ U) (e : MonoidAlgebra ℂ Γ) (he : ∀ a, e * a = a * e) (x : Γ) (u : U) :
    ρ.asAlgebraHom e (ρ x u) = ρ x (ρ.asAlgebraHom e u) := by
  have := congrArg (fun a => ρ.asAlgebraHom a u) (he (MonoidAlgebra.single x 1))
  simpa using this

def cut (ρ : Representation ℂ Γ U) (e : MonoidAlgebra ℂ Γ) (he : ∀ a, e * a = a * e) :
    Representation ℂ Γ (LinearMap.range (ρ.asAlgebraHom e)) :=
  ρ.subrepresentation _ (by
    rintro x _ ⟨u, rfl⟩
    exact ⟨ρ x u, central_comm ρ e he x u⟩)

theorem cut_apply (ρ : Representation ℂ Γ U) (e : MonoidAlgebra ℂ Γ) (he : ∀ a, e * a = a * e) (x : Γ)
    (u : LinearMap.range (ρ.asAlgebraHom e)) : (cut ρ e he x u : U) = ρ x u := rfl

theorem cut_idem (ρ : Representation ℂ Γ U) (e : MonoidAlgebra ℂ Γ) (he : ∀ a, e * a = a * e) (hi : e * e = e)
    (u : LinearMap.range (ρ.asAlgebraHom e)) : (cut ρ e he).asAlgebraHom e u = u := by
  apply Subtype.ext
  have := map_asAlgebraHom (cut ρ e he) ρ (Submodule.subtype _) (fun _ _ => rfl) e u
  simp only [Submodule.subtype_apply] at this
  rw [this]
  obtain ⟨_, v, rfl⟩ := u
  have := congrArg (fun a => ρ.asAlgebraHom a v) hi
  simpa using this

theorem eq_zero_of_mem_ker (ρ : Representation ℂ K U)
    (hfin : ∀ u, ∃ N : Subgroup K, N.FiniteIndex ∧ ∀ k ∈ N, ρ k u = u)
    (v : U) (hv : ∀ k, ρ k v = v) (h0 : v ∈ Representation.Coinvariants.ker ρ) : v = 0 := by
  have P : ∀ u ∈ Representation.Coinvariants.ker ρ, ∃ N : Subgroup K, N.FiniteIndex ∧
      ∀ (N' : Subgroup K) [N'.Normal] [Fintype (K ⧸ N')], N' ≤ N → ∑ q : K ⧸ N', ρ q.out u = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨k, w⟩, rfl⟩ := hx
      obtain ⟨N, hN, hw⟩ := hfin w
      refine ⟨N, hN, fun N' _ _ hle => ?_⟩
      simp only [map_sub, Finset.sum_sub_distrib, sub_eq_zero]
      rw [← Equiv.sum_comp (Equiv.mulRight (k : K ⧸ N')) (fun q : K ⧸ N' => ρ q.out w)]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Equiv.coe_mulRight]
      have h1 : (q.out * k)⁻¹ * (q * (k : K ⧸ N')).out ∈ N' := by
        rw [← QuotientGroup.eq]; simp
      have h2 : (q * (k : K ⧸ N')).out = q.out * k * ((q.out * k)⁻¹ * (q * (k : K ⧸ N')).out) := by group
      rw [h2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw _ (hle h1)]
    | zero => exact ⟨⊤, inferInstance, fun N' _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨N₁, h₁, hx⟩ := hx
      obtain ⟨N₂, h₂, hy⟩ := hy
      refine ⟨N₁ ⊓ N₂, inferInstance, fun N' _ _ hle => ?_⟩
      simp only [map_add, Finset.sum_add_distrib]
      rw [hx N' (hle.trans inf_le_left), hy N' (hle.trans inf_le_right), add_zero]
    | smul c x _ hx =>
      obtain ⟨N₁, h₁, hx⟩ := hx
      refine ⟨N₁, h₁, fun N' _ _ hle => ?_⟩
      simp only [map_smul, ← Finset.smul_sum]
      rw [hx N' hle, smul_zero]
  obtain ⟨N, hN, h⟩ := P v h0
  letI : Fintype (K ⧸ N.normalCore) := Fintype.ofFinite _
  have := h N.normalCore N.normalCore_le
  simp only [hv, Finset.sum_const, Finset.card_univ] at this
  rw [← Nat.cast_smul_eq_nsmul ℂ] at this
  exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

end Abstract

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

theorem opp (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) (W W' : Type) [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Gn g n) W) (ρ' : Representation ℂ (Gn g n) W')
    (T : W →ₗ[ℂ] W') (a : Fin n → ℤ) (f f' : (ZMod g)[X])
    (h1 : ∀ u : Gn g n, (∀ i j, ¬ a i < a j → (u : Mt g n) i j = (1 : Mt g n) i j) → ∀ w, T (ρ u w) = T w)
    (h2 : ∀ u : Gn g n, (∀ i j, ¬ a j < a i → (u : Mt g n) i j = (1 : Mt g n) i j) → ∀ w, ρ' u (T w) = T w)
    (h3 : ∀ m : Gn g n, (∀ i j, a i ≠ a j → (m : Mt g n) i j = 0) → ∀ w, T (ρ m w) = ρ' m (T w))
    (w : W) (hw : ρ'.asAlgebraHom (eSerC L n f') (T (ρ.asAlgebraHom (eSerC L n f) w)) ≠ 0) : f = f' := by
  obtain ⟨hi, hc, -⟩ := GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n
  refine GlobalTheory.T.intertwiner_unipotent_invariant g L h5 hG n _ _ (cut ρ _ (hc f)) (cut ρ' _ (hc f'))
    ((ρ'.asAlgebraHom (eSerC L n f')).rangeRestrict ∘ₗ T ∘ₗ Submodule.subtype _) a f f' ?_ ?_ ?_
    (cut_idem _ _ _ (hi f)) (cut_idem _ _ _ (hi f')) ?_
  · intro u hu
    ext w
    simp [cut_apply, h1 u hu]
  · intro u hu
    ext w
    simp [cut_apply, ← central_comm ρ' _ (hc f'), h2 u hu]
  · intro u hu
    ext w
    simp [cut_apply, ← central_comm ρ' _ (hc f'), h3 u hu]
  · intro h
    apply hw
    have := congrArg Subtype.val (LinearMap.congr_fun h ⟨_, w, rfl⟩)
    simpa using this

def dg (g : ℕ) [Fact g.Prime] {n : ℕ} (a : Fin n → ℤ) : GL (Fin n) ℚ_[g] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i => (g : ℚ_[g]) ^ a i) (by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero))

theorem dg_val (a : Fin n → ℤ) :
    (dg g a : Matrix (Fin n) (Fin n) ℚ_[g]) = Matrix.diagonal fun i => (g : ℚ_[g]) ^ a i := rfl

theorem gne : (g : ℚ_[g]) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero

theorem dg_mul_neg (a : Fin n → ℤ) : dg g a * dg g (-a) = 1 := by
  apply Units.ext
  simp [dg_val, Matrix.diagonal_mul_diagonal, zpow_ne_zero _ gne]

theorem dg_neg (a : Fin n → ℤ) : dg g (-a) = (dg g a)⁻¹ := eq_inv_of_mul_eq_one_right (dg_mul_neg a)

theorem inc_val (k : GL (Fin n) ℤ_[g]) (i j : Fin n) :
    (inc g n k : Matrix (Fin n) (Fin n) ℚ_[g]) i j = ((k : Matrix (Fin n) (Fin n) ℤ_[g]) i j : ℚ_[g]) := rfl

theorem red_val (k : GL (Fin n) ℤ_[g]) (i j : Fin n) :
    (red g n k : Mt g n) i j = PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]) i j) := rfl

theorem exists_conj (a : Fin n → ℤ) (k : GL (Fin n) ℤ_[g]) (M : Matrix (Fin n) (Fin n) ℤ_[g])
    (h : ∀ i j, (M i j : ℚ_[g]) = (g : ℚ_[g]) ^ (a i - a j) * ((k : Matrix (Fin n) (Fin n) ℤ_[g]) i j : ℚ_[g])) :
    ∃ k' : GL (Fin n) ℤ_[g], (k' : Matrix (Fin n) (Fin n) ℤ_[g]) = M ∧ dg g a * inc g n k = inc g n k' * dg g a := by
  have e : (dg g a : Matrix (Fin n) (Fin n) ℚ_[g]) * (algebraMap ℤ_[g] ℚ_[g]).mapMatrix (k : Matrix (Fin n) (Fin n) ℤ_[g]) =
      (algebraMap ℤ_[g] ℚ_[g]).mapMatrix M * (dg g a : Matrix (Fin n) (Fin n) ℚ_[g]) := by
    ext i j
    simp only [dg_val, Matrix.diagonal_mul, Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply,
      PadicInt.algebraMap_apply, h, zpow_sub₀ gne]
    have := zpow_ne_zero (a j) (gne (g := g))
    field_simp
  have hd : M.det = (k : Matrix (Fin n) (Fin n) ℤ_[g]).det := by
    have := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det, mul_comm] at this
    have h2 := mul_right_cancel₀ (Matrix.GeneralLinearGroup.det_ne_zero (dg g a)) this
    exact (IsFractionRing.injective ℤ_[g] ℚ_[g] h2).symm
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hd, ← Matrix.isUnit_iff_isUnit_det]
    exact k.isUnit
  refine ⟨hu.unit, rfl, ?_⟩
  apply Units.ext
  exact e

theorem exists_lift (x : Gn g n) : ∃ k : GL (Fin n) ℤ_[g], red g n k = x ∧
    ∀ i j, (x : Mt g n) i j = 0 → (k : Matrix (Fin n) (Fin n) ℤ_[g]) i j = 0 := by
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun i j => (((x : Mt g n) i j).val : ℤ_[g])
  have hM : (PadicInt.toZMod (p := g)).mapMatrix M = (x : Mt g n) := by
    ext i j
    change PadicInt.toZMod (((x : Mt g n) i j).val : ℤ_[g]) = _
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    by_contra hn
    have h1 : M.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]; exact hn
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    exact Matrix.GeneralLinearGroup.det_ne_zero x h1
  refine ⟨hu.unit, Units.ext hM, fun i j h => ?_⟩
  change M i j = 0
  simp [M, h]

theorem red_surj : Function.Surjective (red g n) := fun x => (exists_lift x).imp fun _ h => h.1

theorem exists_par (a : Fin n → ℤ) (x y : Gn g n) (hx : ∀ i j, a i < a j → (x : Mt g n) i j = 0)
    (hy : ∀ i j, (y : Mt g n) i j = if a i = a j then (x : Mt g n) i j else 0) :
    ∃ k k' : GL (Fin n) ℤ_[g], red g n k = x ∧ red g n k' = y ∧ dg g a * inc g n k = inc g n k' * dg g a := by
  obtain ⟨k, hk, h0⟩ := exists_lift x
  obtain ⟨k', hk', e⟩ := exists_conj a k
    (fun i j => (g : ℤ_[g]) ^ (a i - a j).toNat * (k : Matrix (Fin n) (Fin n) ℤ_[g]) i j) (by
      intro i j
      by_cases h : a i < a j
      · simp [h0 i j (hx i j h)]
      · have : (a i - a j) = ((a i - a j).toNat : ℤ) := by omega
        conv_rhs => rw [this, zpow_natCast]
        simp)
  refine ⟨k, k', hk, ?_, e⟩
  apply Units.ext
  ext i j
  rw [red_val, hk', hy, ← hk, red_val]
  rcases lt_trichotomy (a i) (a j) with h | h | h
  · simp [h0 i j (hx i j h)]
  · simp [h]
  · have : (a i - a j).toNat ≠ 0 := by omega
    simp [h.ne', this]

theorem exists_deep (a : Fin n → ℤ) : ∃ N : Subgroup (GL (Fin n) ℤ_[g]), N.FiniteIndex ∧ N.Normal ∧ ∀ k ∈ N,
    ∃ k' : GL (Fin n) ℤ_[g], red g n k' = 1 ∧ dg g a * inc g n k = inc g n k' * dg g a := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ i j, 0 < (m : ℤ) + (a i - a j) := by
    obtain ⟨b, hb⟩ := (Set.finite_range fun p : Fin n × Fin n => a p.2 - a p.1).bddAbove
    refine ⟨b.toNat + 1, fun i j => ?_⟩
    have := hb (Set.mem_range_self (i, j))
    simp only at this
    omega
  haveI : NeZero (g ^ m) := ⟨pow_ne_zero _ (Fact.out : g.Prime).ne_zero⟩
  refine ⟨(Matrix.GeneralLinearGroup.map (n := Fin n) (PadicInt.toZModPow (p := g) m)).ker,
    inferInstance, inferInstance, fun k hk => ?_⟩
  have hk' : ∀ i j, ∃ c : ℤ_[g], (k : Matrix (Fin n) (Fin n) ℤ_[g]) i j =
      (1 : Matrix (Fin n) (Fin n) ℤ_[g]) i j + c * g ^ m := by
    intro i j
    have h1 : (k : Matrix (Fin n) (Fin n) ℤ_[g]) i j - (1 : Matrix (Fin n) (Fin n) ℤ_[g]) i j ∈
        RingHom.ker (PadicInt.toZModPow (p := g) m) := by
      have h2 : PadicInt.toZModPow (p := g) m ((k : Matrix (Fin n) (Fin n) ℤ_[g]) i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (g ^ m))) i j :=
        by
        have h3 := MonoidHom.mem_ker.1 hk
        have h4 := congrArg (fun z : GL (Fin n) (ZMod (g ^ m)) => (z : Matrix (Fin n) (Fin n) (ZMod (g ^ m))) i j) h3
        exact h4
      rw [RingHom.mem_ker, map_sub, h2]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [hc]; ring⟩
  choose c hc using hk'
  obtain ⟨k', hk', e⟩ := exists_conj a k
    (fun i j => (1 : Matrix (Fin n) (Fin n) ℤ_[g]) i j + c i j * g ^ ((m : ℤ) + (a i - a j)).toNat) (by
      intro i j
      have h1 : ((g : ℚ_[g])) ^ ((m : ℤ) + (a i - a j)).toNat = g ^ m * g ^ (a i - a j) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (hm i j).le, zpow_add₀ gne, zpow_natCast]
      rw [hc]
      push_cast
      rw [h1]
      by_cases h : i = j
      · subst h; simp
      · simp [h]; ring)
  refine ⟨k', ?_, e⟩
  apply Units.ext
  ext i j
  have : ((m : ℤ) + (a i - a j)).toNat ≠ 0 := by have := hm i j; omega
  rw [red_val, hk']
  simp only [map_add, map_mul, map_pow, map_natCast, ZMod.natCast_self, zero_pow this]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_principalCongruenceFixedVectors_iff (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (v : V) :
    v ∈ fixK1 π ↔ ∀ k, red g n k = 1 → π (inc g n k) v = v := by
  simp [fixK1, Submodule.mem_iInf, sub_eq_zero]

theorem fixK1_stable (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (k : GL (Fin n) ℤ_[g]) (v : V)
    (hv : v ∈ fixK1 π) : π (inc g n k) v ∈ fixK1 π := by
  rw [mem_principalCongruenceFixedVectors_iff] at hv ⊢
  intro s hs
  have h1 : s * k = k * (k⁻¹ * s * k) := by group
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, h1, map_mul, map_mul, Module.End.mul_apply,
    hv (k⁻¹ * s * k) (by simp [hs])]

theorem cartan (x : GL (Fin n) ℚ_[g]) : ∃ (k k' : GL (Fin n) ℤ_[g]) (a : Fin n → ℤ),
    x = inc g n k * dg g a * inc g n k' := by
  obtain ⟨k, k', a, -, h⟩ := GlobalTheory.GLp.cartan_decomposition g n x
  exact ⟨k, k', a, Units.ext h⟩

theorem finiteIndex_stab (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (hπ : IsIrrRep π) (w : V) (hw : w ∈ fixK1 π)
    (h0 : w ≠ 0) (u : V) : ∃ N : Subgroup (GL (Fin n) ℤ_[g]), N.FiniteIndex ∧ ∀ k ∈ N, π (inc g n k) u = u := by
  let F : Submodule ℂ V :=
    { carrier := {u | ∀ x, ∃ N : Subgroup (GL (Fin n) ℤ_[g]), N.FiniteIndex ∧ ∀ k ∈ N, π (inc g n k) (π x u) = π x u}
      zero_mem' := fun x => ⟨⊤, inferInstance, by simp⟩
      add_mem' := by
        intro a b ha hb x
        obtain ⟨N₁, h₁, ha⟩ := ha x
        obtain ⟨N₂, h₂, hb⟩ := hb x
        exact ⟨N₁ ⊓ N₂, inferInstance, fun k hk => by simp [ha k hk.1, hb k hk.2]⟩
      smul_mem' := by
        intro c a ha x
        obtain ⟨N₁, h₁, ha⟩ := ha x
        exact ⟨N₁, h₁, fun k hk => by simp [ha k hk]⟩ }
  have hwF : w ∈ F := by
    intro x
    obtain ⟨k, k', a, rfl⟩ := cartan x
    obtain ⟨N, hN, hn, h⟩ := exists_deep (g := g) (-a)
    refine ⟨N, hN, fun s hs => ?_⟩
    obtain ⟨t, ht, e⟩ := h (k⁻¹ * s * k) (by simpa using hn.conj_mem s hs k⁻¹)
    have e2 : inc g n s * (inc g n k * dg g a) = inc g n k * dg g a * inc g n t := by
      rw [dg_neg, map_mul, map_mul, map_inv] at e
      have : inc g n t = (dg g a)⁻¹ * ((inc g n k)⁻¹ * inc g n s * inc g n k) * dg g a := by rw [e]; group
      rw [this]; group
    have h1 := (mem_principalCongruenceFixedVectors_iff π _).1 (fixK1_stable π k' w hw) t ht
    rw [map_mul π, Module.End.mul_apply, ← Module.End.mul_apply (π (inc g n s)), ← map_mul, e2, map_mul π,
      Module.End.mul_apply, h1]
  rcases hπ.2 F (fun x v hv y => by simpa [← Module.End.mul_apply, ← map_mul] using hv (y * x)) with h | h
  · rw [h] at hwF; exact absurd hwF h0
  · have : u ∈ F := h ▸ Submodule.mem_top
    simpa using this 1

theorem label_unique : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V), IsIrrRep π → ∀ f f', HasLab L π f → HasLab L π f' → f = f' := by
  intro g _ L h5 hG n V _ _ π hπ f f' ⟨v, hv, hf⟩ ⟨v', hv', hf'⟩
  obtain ⟨-, hc, -⟩ := GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n
  let ρ : Representation ℂ (GL (Fin n) ℤ_[g]) V := π.comp (inc g n)
  let S := (red g n).ker
  obtain ⟨σ, hσ⟩ := exists_descend (red g n) red_surj
    (ρ.subrepresentation (fixK1 π) (fun k v hv => fixK1_stable π k v hv))
    (fun s hs u => Subtype.ext ((mem_principalCongruenceFixedVectors_iff π _).1 u.2 s hs))
  have hσ' : ∀ k (u : fixK1 π), (σ (red g n k) u : V) = π (inc g n k) u := fun k u => by rw [hσ]; rfl
  obtain ⟨τ, hτ⟩ := exists_descend (red g n) red_surj (ρ.toCoinvariants S) (fun s hs u => by
    obtain ⟨u, rfl⟩ := Representation.Coinvariants.mk_surjective _ u
    exact Representation.Coinvariants.mk_self_apply (ρ.comp S.subtype) ⟨s, hs⟩ u)
  set mk := Representation.Coinvariants.mk (ρ.comp S.subtype) with hmk
  have hτ' : ∀ k u, τ (red g n k) (mk u) = mk (π (inc g n k) u) := fun k u => by rw [hτ]; rfl
  have hact : ∀ a (u : fixK1 π), (σ.asAlgebraHom a u : V) = actK π a u := by
    intro a u
    rw [asAlgebraHom_eq_sum, actK]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lift, ← hσ', Function.rightInverse_invFun red_surj x]
  have hv0 : v ≠ 0 := by rintro rfl; simp at hf
  have hinj : ∀ u : fixK1 π, mk u = 0 → (u : V) = 0 := by
    intro u hu
    refine eq_zero_of_mem_ker (ρ.comp S.subtype) (fun w => ?_) u (fun s => (mem_principalCongruenceFixedVectors_iff π _).1 u.2 s s.2)
      ((Representation.Coinvariants.mk_eq_zero _).1 hu)
    obtain ⟨N, hN, h⟩ := finiteIndex_stab π hπ v hv hv0 w
    exact ⟨N.subgroupOf S, inferInstance, fun k hk => h k hk⟩
  let Φ := τ.asAlgebraHom (eSerC L n f') ∘ₗ mk
  have hΦ : Φ v' ≠ 0 := by
    intro h
    apply hf'
    rw [← hact _ ⟨v', hv'⟩]
    apply hinj
    rw [← h]
    refine map_asAlgebraHom σ τ (mk ∘ₗ (fixK1 π).subtype) (fun x u => ?_) _ ⟨v', hv'⟩
    obtain ⟨k, rfl⟩ := red_surj x
    simp [hσ', hτ']
  let Z : Submodule ℂ V := ⨅ x, LinearMap.ker (Φ ∘ₗ π x)
  have hZ : ∀ u, u ∈ Z ↔ ∀ x, Φ (π x u) = 0 := fun u => by simp [Z, Submodule.mem_iInf]
  have hZ0 : Z = ⊥ := by
    refine (hπ.2 Z fun x u hu => ?_).resolve_right fun h => hΦ ?_
    · rw [hZ] at hu ⊢
      intro y
      simpa using hu (y * x)
    · simpa using (hZ v').1 (h ▸ Submodule.mem_top) 1
  obtain ⟨x, hx⟩ : ∃ x, Φ (π x (actK π (eSerC L n f) v)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (by simpa [hZ0] using (hZ _).2 h)
  obtain ⟨k, k', a, rfl⟩ := cartan x
  let T := mk ∘ₗ π (dg g a) ∘ₗ (fixK1 π).subtype
  have hT : ∀ u : fixK1 π, T u = mk (π (dg g a) u) := fun _ => rfl
  have hconj : ∀ s s' : GL (Fin n) ℤ_[g], dg g a * inc g n s = inc g n s' * dg g a →
      ∀ w, T (σ (red g n s) w) = τ (red g n s') (T w) := by
    intro s s' e w
    rw [hT, hT, hσ', hτ', ← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
  refine opp L h5 hG _ _ σ τ T (-a) f f' ?_ ?_ ?_ (σ (red g n k') ⟨v, hv⟩) ?_
  · intro u hu w
    obtain ⟨s, s', rfl, h1, e⟩ := exists_par a u 1 (fun i j h => by
      rw [hu i j (by simp; omega), Matrix.one_apply_ne (by rintro rfl; omega)]) (fun i j => by
      split_ifs with h
      · rw [hu i j (by simp; omega)]; rfl
      · exact Matrix.one_apply_ne (by rintro rfl; exact h rfl))
    rw [hconj s s' e, h1]; simp
  · intro u hu w
    obtain ⟨s, s', rfl, h1, e⟩ := exists_par (-a) u 1 (fun i j h => by
      rw [hu i j (by omega), Matrix.one_apply_ne (by rintro rfl; omega)]) (fun i j => by
      split_ifs with h
      · rw [hu i j (by omega)]; rfl
      · exact Matrix.one_apply_ne (by rintro rfl; exact h rfl))
    have e2 : dg g a * inc g n s' = inc g n s * dg g a := by
      rw [dg_neg] at e
      have : inc g n s' = (dg g a)⁻¹ * inc g n s * dg g a := by rw [e]; group
      rw [this]; group
    rw [← hconj s' s e2, h1]; simp
  · intro m hm w
    obtain ⟨s, s', h1, h2, e⟩ := exists_par a m m (fun i j h => hm i j (by simp; omega)) (fun i j => by
      split_ifs with h
      · rfl
      · exact hm i j (by simpa using h))
    have := hconj s s' e w
    rwa [h1, h2] at this
  · intro h
    apply hx
    rw [central_comm σ _ (hc f), hT, hσ', hact] at h
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    change τ.asAlgebraHom _ (mk _) = 0
    rw [← hτ', central_comm τ _ (hc f'), h, map_zero]

end GlobalTheory.GLp.OneLabel
end
end

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_unique_of_irreducible : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V), IsIrrRep π → ∀ f f', HasLab L π f → HasLab L π f' → f = f' := by
  atlas_forward_decl GlobalTheory.GLp.OneLabel.label_unique
end

section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp.ParInd

section Blocks
variable {R : Type} [CommRing R] {a b : ℕ}

theorem entN_tl (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin a) :
    entN M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_br (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin b) :
    entN M (a + i) (a + j) = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_self {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) : entN M i j = M i j := by
  simp [entN]

theorem det_par (M : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0) :
    M.det = (Matrix.of fun i j : Fin a => entN M i j).det *
      (Matrix.of fun i j : Fin b => entN M (a + i) (a + j)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    apply h <;> simp
  rw [h0, Matrix.det_fromBlocks_zero₂₁]
  congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, entN_tl, entN_br]

theorem exists_blocks (p : GL (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix _ _ R) i j = 0) :
    ∃ (x : GL (Fin a) R) (y : GL (Fin b) R),
      (∀ i j : Fin a, (x : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) i j) ∧
      (∀ i j : Fin b, (y : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) (a + i) (a + j)) := by
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [det_par _ h] at hu
  have h1 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hu)
  have h2 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)
  exact ⟨h1.unit, h2.unit, fun i j => by simp, fun i j => by simp⟩

def dg (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  fun i j => if (i : ℕ) < a ∧ (j : ℕ) < a then entN x i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then entN y (i - a) (j - a) else 0

theorem dg_par (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin (a + b))
    (hj : (j : ℕ) < a) (hi : a ≤ (i : ℕ)) : dg x y i j = 0 := by
  unfold dg
  rw [if_neg (by omega), if_neg (by omega)]

theorem dg_tl (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin a) :
    entN (dg x y) i j = x i j := by
  rw [entN_tl]
  simp [dg, entN_self]

theorem dg_br (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin b) :
    entN (dg x y) (a + i) (a + j) = y i j := by
  rw [entN_br]
  simp [dg, entN_self]

theorem dg_det (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) :
    (dg x y).det = x.det * y.det := by
  rw [det_par _ (dg_par x y)]
  congr 2 <;> ext i j <;> simp [dg_tl, dg_br]

theorem dg_unit (x : GL (Fin a) R) (y : GL (Fin b) R) : IsUnit (dg x.val y.val) := by
  rw [Matrix.isUnit_iff_isUnit_det, dg_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit)

theorem dg_one : dg (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [← entN_tl (dg 1 1), dg_tl]; simp [Matrix.one_apply]
  · rw [Matrix.one_apply_ne (by intro h; have := congrArg Fin.val h; simp at this; omega)]
    simp [dg]
  · rw [Matrix.one_apply_ne (by intro h; have := congrArg Fin.val h; simp at this; omega)]
    simp [dg]
  · rw [← entN_br (dg 1 1), dg_br]; simp [Matrix.one_apply]

theorem entN_map {S : Type} [CommRing S] (f : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : ℕ) :
    entN (M.map f) i j = f (entN M i j) := by
  unfold entN
  split_ifs <;> simp

theorem dg_map {S : Type} [CommRing S] (f : R →+* S) (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) :
    (dg x y).map f = dg (x.map f) (y.map f) := by
  ext i j
  simp only [dg, Matrix.map_apply, entN_map]
  split_ifs <;> simp

theorem mul_par (M N : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (hM : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0)
    (hN : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → N i j = 0) (i j : Fin (a + b))
    (hj : (j : ℕ) < a) (hi : a ≤ (i : ℕ)) : (M * N) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < a
  · rw [hM i k hk hi, zero_mul]
  · rw [hN k j hj (by omega), mul_zero]

theorem mul_tl (M N : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (hN : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → N i j = 0) (i j : Fin a) :
    entN (M * N) i j = ∑ k : Fin a, entN M i k * entN N k j := by
  simp only [entN_tl, Matrix.mul_apply, Fin.sum_univ_add]
  rw [Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin b))), add_zero]
  intro k _
  rw [hN _ _ (by simp) (by simp), mul_zero]

end Blocks

variable {g : ℕ} [Fact g.Prime] {a b : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem inc_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (inc g n k).val = k.val.map (algebraMap ℤ_[g] ℚ_[g]) := rfl

theorem red_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (red g n k).val = k.val.map (PadicInt.toZMod (p := g)) := rfl

theorem det_inc (n : ℕ) (k : GL (Fin n) ℤ_[g]) : Matrix.GeneralLinearGroup.det (inc g n k) =
    Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, inc_val, Units.coe_map]
  exact ((algebraMap ℤ_[g] ℚ_[g]).map_det k.val).symm

theorem det_red (n : ℕ) (k : GL (Fin n) ℤ_[g]) : Matrix.GeneralLinearGroup.det (red g n k) =
    Units.map (PadicInt.toZMod (p := g)).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, red_val, Units.coe_map]
  exact ((PadicInt.toZMod (p := g)).map_det k.val).symm

theorem mem_principalCongruenceFixedVectors_iff {n : ℕ} (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (v : V) :
    v ∈ fixK1 π ↔ ∀ k, red g n k = 1 → π (inc g n k) v = v := by
  simp [fixK1, Submodule.mem_iInf, sub_eq_zero, MonoidHom.mem_ker]

theorem exists_par_lift {n : ℕ} (a : ℕ) (p : Gn g n) (hp : InPar a (p : Mt g n)) :
    ∃ k : GL (Fin n) ℤ_[g], red g n k = p ∧ ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → k.val i j = 0 := by
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := Matrix.of fun i j => ((p.val i j).val : ℤ_[g])
  have hM : M.map (PadicInt.toZMod (p := g)) = p.val := by
    ext i j
    simp [M]
  have hd : PadicInt.toZMod (p := g) M.det = p.val.det := by
    rw [RingHom.map_det, ← hM]; rfl
  have hu : IsUnit M.det := by
    by_contra hn
    have : M.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]; exact hn
    rw [RingHom.mem_ker, hd] at this
    exact ((Matrix.isUnit_iff_isUnit_det _).1 p.isUnit).ne_zero this
  have hu' := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨hu'.unit, ?_, fun i j hj hi => ?_⟩
  · ext1
    rw [red_val, IsUnit.unit_spec, hM]
  · rw [IsUnit.unit_spec]
    simp [M, hp i j hj hi]

def Eqv (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W) : Prop :=
  ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
    (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → p.val i j = 0) →
    (∀ i j : Fin a, x.val i j = entN p.val i j) →
    (∀ i j : Fin b, y.val i j = entN p.val (a + i) (a + j)) →
    ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
      σ x (Λ v)

variable {π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V} {σ : Representation ℂ (GL (Fin a) ℚ_[g]) W}
  {ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ} {Λ : V →ₗ[ℂ] W} {χ : (ZMod g)ˣ →* ℂˣ}

theorem eqv_int (hΛ : Eqv π σ ν₁ ν₂ Λ)
    (h1 : ∀ u : ℤ_[g]ˣ, ν₁ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1)
    (h2 : ∀ u : ℤ_[g]ˣ, ν₂ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) =
      χ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (k : GL (Fin (a + b)) ℤ_[g]) (x : GL (Fin a) ℤ_[g]) (y : GL (Fin b) ℤ_[g])
    (hk : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → k.val i j = 0)
    (hx : ∀ i j : Fin a, x.val i j = entN k.val i j)
    (hy : ∀ i j : Fin b, y.val i j = entN k.val (a + i) (a + j)) (v : V) :
    Λ (π (inc g _ k) v) = ((χ (Matrix.GeneralLinearGroup.det (red g b y)) : ℂˣ) : ℂ) • σ (inc g a x) (Λ v) := by
  rw [hΛ (inc g _ k) (inc g a x) (inc g b y), det_inc, det_inc, h1, h2, det_red, one_mul]
  · intro i j hj hi
    rw [inc_val, Matrix.map_apply, hk i j hj hi, map_zero]
  · intro i j
    rw [inc_val, inc_val, entN_map, Matrix.map_apply, hx]
  · intro i j
    rw [inc_val, inc_val, entN_map, Matrix.map_apply, hy]

theorem map_fix (hΛ : Eqv π σ ν₁ ν₂ Λ)
    (h1 : ∀ u : ℤ_[g]ˣ, ν₁ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1)
    (h2 : ∀ u : ℤ_[g]ˣ, ν₂ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) =
      χ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (v : V) (hv : v ∈ fixK1 π) : Λ v ∈ fixK1 σ := by
  rw [mem_principalCongruenceFixedVectors_iff] at hv ⊢
  intro x hx
  have hu := dg_unit x (1 : GL (Fin b) ℤ_[g])
  have h := eqv_int hΛ h1 h2 hu.unit x 1 (fun i j hj hi => by rw [IsUnit.unit_spec]; exact dg_par _ _ i j hj hi)
    (fun i j => by rw [IsUnit.unit_spec, dg_tl]) (fun i j => by rw [IsUnit.unit_spec, dg_br]) v
  rw [hv] at h
  · simpa using h.symm
  · ext1
    rw [red_val, IsUnit.unit_spec, dg_map, ← red_val, ← red_val, hx, map_one]
    exact dg_one

theorem eqv_fin (hΛ : Eqv π σ ν₁ ν₂ Λ)
    (h1 : ∀ u : ℤ_[g]ˣ, ν₁ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1)
    (h2 : ∀ u : ℤ_[g]ˣ, ν₂ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) =
      χ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (p : Gn g (a + b)) (x : Gn g a) (y : Gn g b) (hp : InPar a p.val)
    (hx : ∀ i j : Fin a, x.val i j = entN p.val i j)
    (hy : ∀ i j : Fin b, y.val i j = entN p.val (a + i) (a + j)) (v : V) (hv : v ∈ fixK1 π) :
    Λ (π (lift g _ p) v) = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • σ (lift g a x) (Λ v) := by
  obtain ⟨k, rfl, hk⟩ := exists_par_lift a p hp
  obtain ⟨x', y', hx', hy'⟩ := exists_blocks k hk
  have ex : red g a x' = x := by
    ext i j
    rw [hx, red_val, red_val, entN_map, Matrix.map_apply, hx']
  have ey : red g b y' = y := by
    ext i j
    rw [hy, red_val, red_val, entN_map, Matrix.map_apply, hy']
  rw [← ((GlobalTheory.GLp.finite_group_acts_on_fixK1 g _ V π).2 v hv).2.1, eqv_int hΛ h1 h2 k x' y' hk hx' hy', ey,
    ((GlobalTheory.GLp.finite_group_acts_on_fixK1 g _ W σ).2 _ (map_fix hΛ h1 h2 v hv)).2.1, ex]

theorem blk_val (x : Gn g a) (y : Gn g b) : (blk a b (a + b) x y).val = dg x.val y.val := by
  have hu := dg_unit x y
  change (toG (dg x.val y.val)).val = _
  rw [toG, dif_pos hu, IsUnit.unit_spec]

def InQ (a : ℕ) {n : ℕ} (p : Gn g n) : Prop := InPar a p.val ∧ tl a p.val = 1

theorem InQ.ent {p : Gn g (a + b)} (hp : InQ a p) (i j : Fin a) :
    entN p.val i j = (1 : Matrix (Fin a) (Fin a) (ZMod g)) i j := by
  rw [← hp.2]; rfl

theorem InQ.mul {p q : Gn g (a + b)} (hp : InQ a p) (hq : InQ a q) : InQ a (p * q) := by
  refine ⟨fun i j hj hi => mul_par _ _ hp.1 hq.1 i j hj hi, ?_⟩
  ext i j
  change entN (p.val * q.val) i j = _
  rw [mul_tl _ _ hq.1]
  simp only [hp.ent, hq.ent]
  rw [← Matrix.mul_apply, one_mul]

theorem InQ.det {p : Gn g (a + b)} (hp : InQ a p) (y : Gn g b)
    (hy : ∀ i j : Fin b, y.val i j = entN p.val (a + i) (a + j)) :
    Matrix.GeneralLinearGroup.det p = Matrix.GeneralLinearGroup.det y := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  rw [det_par _ hp.1]
  have e1 : (Matrix.of fun i j : Fin a => entN p.val i j) = 1 := by ext i j; exact hp.ent i j
  have e2 : (Matrix.of fun i j : Fin b => entN p.val (a + i) (a + j)) = y.val := by ext i j; exact (hy i j).symm
  rw [e1, e2, Matrix.det_one, one_mul]

theorem lift_one {n : ℕ} (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (v : V) (hv : v ∈ fixK1 π) :
    π (lift g n 1) v = v := by
  have := ((GlobalTheory.GLp.finite_group_acts_on_fixK1 g _ V π).2 v hv).2.1 1
  rw [map_one, map_one, map_one] at this
  exact this.symm

theorem exists_parVec (hΛ : Eqv π σ ν₁ ν₂ Λ)
    (h1 : ∀ u : ℤ_[g]ˣ, ν₁ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1)
    (h2 : ∀ u : ℤ_[g]ˣ, ν₂ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) =
      χ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (w : V) (hw : w ∈ fixK1 π) (hw0 : Λ w ≠ 0) : ∃ v, IsParVec π a b χ v ∧ Λ v ≠ 0 := by
  have hb := (GlobalTheory.GLp.finite_group_acts_on_fixK1 g _ V π).2 w hw
  let φ : Gn g (a + b) →* ℂ := (Units.coeHom ℂ).comp (χ.comp Matrix.GeneralLinearGroup.det)
  have hφ : ∀ p, φ p = ((χ (Matrix.GeneralLinearGroup.det p) : ℂˣ) : ℂ) := fun p => rfl
  have hφ0 : ∀ p, φ p ≠ 0 := fun p => by rw [hφ]; exact Units.ne_zero _
  let v : V := ∑ p : {p : Gn g (a + b) // InQ a p}, (φ p.1)⁻¹ • π (lift g _ p.1) w
  have hq : ∀ q : Gn g (a + b), InQ a q → π (lift g _ q) v = φ q • v := by
    intro q hq
    let m : {p : Gn g (a + b) // InQ a p} → {p : Gn g (a + b) // InQ a p} := fun p => ⟨q * p.1, hq.mul p.2⟩
    have hm : Function.Bijective m := Finite.injective_iff_bijective.1 fun p p' h =>
      Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
    have e : v = ∑ p : {p : Gn g (a + b) // InQ a p}, (φ (m p).1)⁻¹ • π (lift g _ (m p).1) w :=
      (hm.sum_comp (fun p => (φ p.1)⁻¹ • π (lift g _ p.1) w)).symm
    conv_rhs => rw [e]
    simp only [v, map_sum, map_smul, Finset.smul_sum, m, smul_smul, map_mul, hb.2.2.1]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    have := hφ0 q
    have := hφ0 p.1
    field_simp
  refine ⟨v, ⟨Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hb.1 _), fun u hu ht hr => ?_, fun y => ?_⟩, ?_⟩
  · rw [hq u ⟨hu, ht⟩, hφ, InQ.det ⟨hu, ht⟩ 1 (fun i j => by rw [Units.val_one, ← hr]; rfl)]
    simp
  · have hy : InQ a (blk a b (a + b) 1 y) := by
      refine ⟨fun i j hj hi => by rw [blk_val]; exact dg_par _ _ i j hj hi, ?_⟩
      ext i j
      rw [blk_val]
      exact dg_tl _ _ i j
    rw [hq _ hy, hφ, hy.det y (fun i j => by rw [blk_val, dg_br])]
  · have e : ∀ p : {p : Gn g (a + b) // InQ a p}, Λ ((φ p.1)⁻¹ • π (lift g _ p.1) w) = Λ w := by
      intro p
      obtain ⟨x, y, -, hy⟩ := exists_blocks p.1 p.2.1
      rw [map_smul, eqv_fin hΛ h1 h2 p.1 1 y p.2.1 (fun i j => (p.2.ent i j).symm) hy w hw,
        lift_one σ _ (map_fix hΛ h1 h2 w hw), smul_smul, ← p.2.det y hy, ← hφ, inv_mul_cancel₀ (hφ0 _), one_smul]
    have hne : Nonempty {p : Gn g (a + b) // InQ a p} := by
      refine ⟨⟨1, fun i j hj hi => ?_, ?_⟩⟩
      · rw [Units.val_one, ← dg_one]; exact dg_par _ _ i j hj hi
      · ext i j
        rw [Units.val_one, ← dg_one]; exact dg_tl _ _ i j
    simp only [v, map_sum, e, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
    refine smul_ne_zero ?_ hw0
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 Finset.univ_nonempty).ne'

end GlobalTheory.GLp.ParInd
end
