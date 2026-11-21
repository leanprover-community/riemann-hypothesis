import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpand
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTens
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA

section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem qdet_slice {n : Fin 2 → ℕ} (h : ∑ i, n i = n 0 + n 1) (τ : E →+* ℂ) (i : Fin 2) (w : ℂ)
    (ψ : Sm E (n 0 + n 1)) (m : ∀ j, GA E (n j)) (θ : Sm E (n i))
    (hθ : ∀ y, ψ.1 (leviEmb (Ad E) (stdBlocks n h) (Function.update m i y)) = θ.1 y) :
    (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)) w ψ).1
      (leviEmb (Ad E) (stdBlocks n h) m) = (Formalism.REAL.qdet (Eop (a := n i) τ) w θ).1 (m i) := by
  have hR : restrLin (stdBlocks n h) m i ψ = θ := Subtype.ext (funext fun y => hθ y)
  have key := LinearMap.congr_fun (qdet_intertwine (restrLin (stdBlocks n h) m i) _ (Eop τ)
    (restrLin_Eop (stdBlocks n h) m i τ) w) ψ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hR] at key
  have k2 := congrArg (fun φ : Sm E (n i) => φ.1 (m i)) key
  have hm : Function.update m i (m i) = m := Function.update_eq_self i m
  have k3 : (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨i, p⟩)
      (stdBlocks n h ⟨i, q⟩)) w ψ).1 (leviEmb (Ad E) (stdBlocks n h) (Function.update m i (m i))) =
      (Formalism.REAL.qdet (Eop (a := n i) τ) w θ).1 (m i) := k2
  rwa [hm] at k3

theorem update_levPair_zero {n : Fin 2 → ℕ} (p : GA E (n 0) × GA E (n 1)) (y : GA E (n 0)) :
    Function.update (CapFactor.levPair p) 0 y = CapFactor.levPair (y, p.2) := by
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

theorem update_levPair_one {n : Fin 2 → ℕ} (p : GA E (n 0) × GA E (n 1)) (y : GA E (n 1)) :
    Function.update (CapFactor.levPair p) 1 y = CapFactor.levPair (p.1, y) := by
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

theorem capR_expand {n : Fin 2 → ℕ} (τ : E →+* ℂ) (w : ℂ) (G : Sm E (n 0 + n 1)) {k : ℕ}
    (b : Fin k → Sm E (n 0)) (q : Fin k → Sm E (n 1))
    (hG : ∀ p, G.1 (lev (Ad E) (n 0) (n 1) p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) (p : GA E (n 0) × GA E (n 1)) :
    (capR (n 0) (n 1) τ w G).1 (lev (Ad E) (n 0) (n 1) p) = ∑ i, (cap τ w (b i)).1 p.1 * (q i).1 p.2 := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  set θ : Sm E (n 0) := ∑ i, (q i).1 p.2 • b i with hθ
  have key := qdet_slice h τ 0 (w + ((n 0 : ℂ) - 1) / 2) G (CapFactor.levPair p) θ (fun y => by
    rw [update_levPair_zero, ← CapFactor.lev_eq_leviEmb n h, hG]
    simp [hθ, Finset.sum_apply, mul_comm])
  have e1 : (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by
    funext p q
    rw [CapFactor.std_zero, CapFactor.std_zero]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  change (capR (n 0) (n 1) τ w G).1 _ = (cap τ w θ).1 p.1 at key
  rw [key, hθ, map_sum]
  simp [Finset.sum_apply, mul_comm]

theorem capS_expand {n : Fin 2 → ℕ} (τ : E →+* ℂ) (w : ℂ) (G : Sm E (n 0 + n 1)) {k : ℕ}
    (b : Fin k → Sm E (n 0)) (q : Fin k → Sm E (n 1))
    (hG : ∀ p, G.1 (lev (Ad E) (n 0) (n 1) p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) (p : GA E (n 0) × GA E (n 1)) :
    (capS (n 0) (n 1) τ w G).1 (lev (Ad E) (n 0) (n 1) p) = ∑ i, (b i).1 p.1 * (cap τ w (q i)).1 p.2 := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  set θ : Sm E (n 1) := ∑ i, (b i).1 p.1 • q i with hθ
  have key := qdet_slice h τ 1 (w + ((n 1 : ℂ) - 1) / 2) G (CapFactor.levPair p) θ (fun y => by
    rw [update_levPair_one, ← CapFactor.lev_eq_leviEmb n h, hG]
    simp [hθ, Finset.sum_apply])
  have e1 : (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by
    funext p q
    rw [CapFactor.std_one, CapFactor.std_one]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  change (capS (n 0) (n 1) τ w G).1 _ = (cap τ w θ).1 p.2 at key
  rw [key, hθ, map_sum]
  simp [Finset.sum_apply]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end

section
noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra

section Ker

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem common_ker (L : List (Module.End ℂ M)) (hL : ∀ N ∈ L, IsNilpotent N)
    (hc : ∀ N ∈ L, ∀ N' ∈ L, Commute N N') (Q : Submodule ℂ M) (hQ : Q ≠ ⊥)
    (hQL : ∀ N ∈ L, ∀ y ∈ Q, N y ∈ Q) : ∃ y ∈ Q, y ≠ 0 ∧ ∀ N ∈ L, N y = 0 := by
  induction L generalizing Q with
  | nil =>
    obtain ⟨y, hy, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
    exact ⟨y, hy, h0, by simp⟩
  | cons N L ih =>
    classical
    obtain ⟨y, hy, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
    obtain ⟨n, hn⟩ := hL N List.mem_cons_self
    have hex : ∃ k, (N ^ k) y = 0 := ⟨n, by rw [hn]; rfl⟩
    set k := Nat.find hex with hk
    have hk0 : k ≠ 0 := by
      intro h
      have h1 := Nat.find_spec hex
      rw [← hk, h, pow_zero, Module.End.one_apply] at h1
      exact h0 h1
    have hpowQ : ∀ j, (N ^ j) y ∈ Q := by
      intro j
      induction j with
      | zero => simpa using hy
      | succ j ihj =>
        rw [pow_succ', Module.End.mul_apply]
        exact hQL N List.mem_cons_self _ ihj
    have hy1 : (N ^ (k - 1)) y ≠ 0 := Nat.find_min hex (by omega)
    have hNy1 : N ((N ^ (k - 1)) y) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
      exact Nat.find_spec hex
    set Q' := Q ⊓ LinearMap.ker N with hQ'
    have hQ'0 : Q' ≠ ⊥ := by
      intro h
      have hm : (N ^ (k - 1)) y ∈ Q' := ⟨hpowQ _, hNy1⟩
      rw [h] at hm
      exact hy1 ((Submodule.mem_bot ℂ).1 hm)
    have hLQ' : ∀ N' ∈ L, ∀ z ∈ Q', N' z ∈ Q' := by
      intro N' hN' z hz
      refine ⟨hQL N' (List.mem_cons_of_mem _ hN') z hz.1, ?_⟩
      change N (N' z) = 0
      rw [← Module.End.mul_apply, (hc N List.mem_cons_self N' (List.mem_cons_of_mem _ hN')).eq,
        Module.End.mul_apply]
      have : N z = 0 := hz.2
      rw [this, map_zero]
    obtain ⟨z, hz, hz0, hzL⟩ := ih (fun N' hN' => hL N' (List.mem_cons_of_mem _ hN'))
      (fun N' hN' N'' hN'' => hc N' (List.mem_cons_of_mem _ hN') N'' (List.mem_cons_of_mem _ hN'')) Q' hQ'0 hLQ'
    refine ⟨z, hz.1, hz0, fun N' hN' => ?_⟩
    rcases List.mem_cons.1 hN' with rfl | h
    · exact hz.2
    · exact hzL N' h

end Ker

section Poly

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem poly_eq (n : ℕ) (a : ℕ → Module.End ℂ M) (ha : a n = 1) (σ : Multiset ℂ) (hσ : σ.Nodup)
    (hc : Multiset.card σ = n) (h : ∀ x ∈ σ, (∑ k ∈ Finset.range (n + 1), (-x) ^ k • a k) = 0) (u : ℂ) :
    (∑ k ∈ Finset.range (n + 1), u ^ k • a k) = (σ.map (u + ·)).prod • (1 : Module.End ℂ M) := by
  classical
  set P : ℂ[X] := (σ.map fun x => X + C x).prod with hP
  have hPm : P.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_add_C x
  have hPd : P.natDegree = n := by
    rw [hP, natDegree_multiset_prod_of_monic _ fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx; exact monic_X_add_C y]
    simp [hc]
  have hPe : ∀ w : ℂ, P.eval w = (σ.map (w + ·)).prod := fun w => by
    simp [hP, eval_multiset_prod, Multiset.map_map]
  have hPsum : ∀ w : ℂ, P.eval w = ∑ k ∈ Finset.range (n + 1), P.coeff k * w ^ k := fun w => by
    rw [eval_eq_sum_range, hPd]
  have hPn : P.coeff n = 1 := by rw [← hPd]; exact hPm.coeff_natDegree
  refine LinearMap.ext fun y => ?_
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
  set g : ℂ[X] := ∑ i : Fin n, C (f (a i y) - f y * P.coeff i) * X ^ (i : ℕ) with hg
  have hge : ∀ w : ℂ, g.eval w = f ((∑ k ∈ Finset.range (n + 1), w ^ k • a k) y) - f y * P.eval w := by
    intro w
    rw [hPsum, hg, eval_finsetSum, Finset.sum_range_succ, Finset.sum_range_succ, hPn, ha,
      LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum, ← Fin.sum_univ_eq_sum_range (fun k => f ((w ^ k • a k) y)),
      ← Fin.sum_univ_eq_sum_range (fun k => P.coeff k * w ^ k)]
    simp only [eval_mul, eval_C, eval_pow, eval_X, LinearMap.smul_apply, map_smul, smul_eq_mul, Module.End.one_apply,
      mul_add, Finset.mul_sum]
    simp only [sub_mul, Finset.sum_sub_distrib, one_mul]
    have h1 : ∑ x : Fin n, f (a x y) * w ^ (x : ℕ) = ∑ x : Fin n, w ^ (x : ℕ) * f (a x y) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have h2 : ∑ x : Fin n, f y * P.coeff x * w ^ (x : ℕ) = ∑ i : Fin n, f y * (P.coeff i * w ^ (i : ℕ)) :=
      Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    rw [h1, h2]
    ring
  have hg0 : g = 0 := by
    by_contra hne
    have hdeg : g.natDegree < n := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact absurd (by simp [hg]) hne
      · rw [natDegree_lt_iff_degree_lt hne]
        exact degree_sum_fin_lt _
    refine hne (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g (σ.map Neg.neg).toFinset (fun w hw => ?_) ?_)
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hw)
      rw [hge, h x hx, LinearMap.zero_apply, map_zero, hPe]
      have : (σ.map (-x + ·)).prod = 0 := Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨x, hx, by ring⟩)
      rw [this, mul_zero, sub_zero]
    · rw [Multiset.toFinset_card_of_nodup (hσ.map neg_injective), Multiset.card_map, hc]
      exact hdeg
  have := hge u
  rw [hg0, eval_zero, hPe] at this
  rw [map_sub, LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_eq_mul]
  linear_combination -this

theorem isUnit_poly (n : ℕ) (a : ℕ → Module.End ℂ M) (χ : ℕ → ℂ) (hcomm : ∀ k l, Commute (a k) (a l))
    (hnil : ∀ k, IsNilpotent (a k - χ k • 1)) (w : ℂ) (hw : (∑ k ∈ Finset.range (n + 1), w ^ k * χ k) ≠ 0) :
    IsUnit (∑ k ∈ Finset.range (n + 1), w ^ k • a k) := by
  set c := ∑ k ∈ Finset.range (n + 1), w ^ k * χ k with hc
  set N := ∑ k ∈ Finset.range (n + 1), w ^ k • (a k - χ k • 1) with hN
  have hNn : IsNilpotent N := by
    refine Commute.isNilpotent_sum (fun k _ => (hnil k).smul _) fun i j _ _ => ?_
    refine ((((hcomm i j).sub_right (Commute.smul_right (Commute.one_right _) _)).sub_left
      (Commute.smul_left (Commute.one_left _) _))).smul_left _ |>.smul_right _
  have e : (∑ k ∈ Finset.range (n + 1), w ^ k • a k) = algebraMap ℂ _ c * (1 + c⁻¹ • N) := by
    rw [mul_add, mul_one, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hw, one_smul, hN, hc, Algebra.algebraMap_eq_smul_one,
      Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_sub, smul_smul, mul_comm, add_sub_cancel]
  rw [e]
  exact ((Units.mk0 c hw).isUnit.map (algebraMap ℂ (Module.End ℂ M))).mul (IsNilpotent.isUnit_one_add (hNn.smul _))

end Poly

section Piece

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem comm_sub {x y : Module.End ℂ M} (h : Commute x y) (c d : ℂ) : Commute (x - c • 1) (y - d • 1) :=
  ((h.sub_right (Commute.smul_right (Commute.one_right _) _)).sub_left
    ((Commute.smul_left (Commute.one_left _) _).sub_right (Commute.smul_right (Commute.one_right _) _)))

theorem apply_eig (n : ℕ) (a : ℕ → Module.End ℂ M) (χ : ℕ → ℂ) (y : M)
    (hy : ∀ k ∈ Finset.range (n + 1), a k y = χ k • y) (u : ℂ) :
    (∑ k ∈ Finset.range (n + 1), u ^ k • a k) y = (∑ k ∈ Finset.range (n + 1), u ^ k * χ k) • y := by
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [LinearMap.smul_apply, hy k hk, smul_smul]

def spoly (n : ℕ) (χ : ℕ → ℂ) : ℂ[X] := X ^ n + ∑ i : Fin n, C (χ i) * X ^ (i : ℕ)

theorem spoly_monic (n : ℕ) (χ : ℕ → ℂ) : (spoly n χ).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

theorem spoly_natDegree (n : ℕ) (χ : ℕ → ℂ) : (spoly n χ).natDegree = n := by
  rw [spoly, natDegree_add_eq_left_of_degree_lt]
  · simp
  · exact (degree_sum_fin_lt _).trans_eq (by simp)

theorem spoly_eval (n : ℕ) (χ : ℕ → ℂ) (h : χ n = 1) (u : ℂ) :
    (spoly n χ).eval u = ∑ k ∈ Finset.range (n + 1), u ^ k * χ k := by
  rw [spoly, eval_add, eval_finsetSum, Finset.sum_range_succ, h, mul_one, add_comm,
    ← Fin.sum_univ_eq_sum_range (fun k => u ^ k * χ k)]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem piece [Nontrivial M] (r s : ℕ) (a b : ℕ → Module.End ℂ M) (haa : ∀ k l, Commute (a k) (a l))
    (hab : ∀ k l, Commute (a k) (b l)) (hbb : ∀ k l, Commute (b k) (b l))
    (ha : a r = 1) (hb : b s = 1) (m : Multiset ℂ) (hm : m.Nodup)
    (hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), u ^ k • a k) * (∑ l ∈ Finset.range (s + 1), u ^ l • b l) =
      (m.map (u + ·)).prod • (1 : Module.End ℂ M))
    (χa χb : ℕ → ℂ) (hna : ∀ k, IsNilpotent (a k - χa k • 1)) (hnb : ∀ l, IsNilpotent (b l - χb l • 1)) :
    ∃ σ : Multiset ℂ, σ ≤ m ∧ Multiset.card σ = r ∧ ∀ u : ℂ,
      (∑ k ∈ Finset.range (r + 1), u ^ k • a k) = (σ.map (u + ·)).prod • 1 ∧
      (∑ l ∈ Finset.range (s + 1), u ^ l • b l) = ((m - σ).map (u + ·)).prod • 1 := by
  classical

  set L : List (Module.End ℂ M) := ((List.range (r + 1)).map fun k => a k - χa k • 1) ++
    (List.range (s + 1)).map fun l => b l - χb l • 1 with hL
  have hLn : ∀ N ∈ L, IsNilpotent N := by
    intro N hN
    rcases List.mem_append.1 hN with h | h
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; exact hna k
    · obtain ⟨l, -, rfl⟩ := List.mem_map.1 h; exact hnb l
  have hLc : ∀ N ∈ L, ∀ N' ∈ L, Commute N N' := by
    intro N hN N' hN'
    rcases List.mem_append.1 hN with h | h <;> rcases List.mem_append.1 hN' with h' | h'
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (haa k l) _ _
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (hab k l) _ _
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (hab l k).symm _ _
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (hbb k l) _ _
  obtain ⟨y, -, hy0, hyL⟩ := common_ker L hLn hLc ⊤ top_ne_bot (fun _ _ _ _ => Submodule.mem_top)
  have hya : ∀ k ∈ Finset.range (r + 1), a k y = χa k • y := fun k hk => by
    have := hyL _ (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 (Finset.mem_range.1 hk), rfl⟩))
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  have hyb : ∀ l ∈ Finset.range (s + 1), b l y = χb l • y := fun l hl => by
    have := hyL _ (List.mem_append_right _ (List.mem_map.2 ⟨l, List.mem_range.2 (Finset.mem_range.1 hl), rfl⟩))
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  have hχa : χa r = 1 := by
    have h1 := hya r (Finset.self_mem_range_succ r)
    rw [ha, Module.End.one_apply] at h1
    exact (smul_left_injective ℂ hy0 (h1.symm.trans (one_smul ℂ y).symm))
  have hχb : χb s = 1 := by
    have h1 := hyb s (Finset.self_mem_range_succ s)
    rw [hb, Module.End.one_apply] at h1
    exact (smul_left_injective ℂ hy0 (h1.symm.trans (one_smul ℂ y).symm))

  set pC := spoly r χa with hpC
  set pD := spoly s χb with hpD
  set S : ℂ[X] := (m.map fun x => X - C (-x)).prod with hS
  have hSe : ∀ u, S.eval u = (m.map (u + ·)).prod := fun u => by
    simp [hS, eval_multiset_prod, Multiset.map_map, sub_neg_eq_add]
  have hscal : ∀ u, pC.eval u * pD.eval u = S.eval u := by
    intro u
    have h1 := congrArg (fun T : Module.End ℂ M => T y) (hrel u)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    rw [apply_eig s b χb y hyb, map_smul, apply_eig r a χa y hya, smul_smul] at h1
    rw [spoly_eval r χa hχa, spoly_eval s χb hχb, hSe, mul_comm]
    exact smul_left_injective ℂ hy0 h1
  have hCD : pC * pD = S := Polynomial.funext fun u => by rw [eval_mul, hscal]
  have hSm : S.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C _
  have hS0 : S ≠ 0 := hSm.ne_zero
  have hSr : S.roots = m.map Neg.neg := by
    have e : (m.map fun x => X - C (-x)) = (m.map Neg.neg).map (fun x => X - C x) := by
      rw [Multiset.map_map]; rfl
    rw [hS, e, roots_multiset_prod_X_sub_C]
  have hroots : pC.roots + pD.roots = m.map Neg.neg := by
    rw [← roots_mul (hCD ▸ hS0), hCD, hSr]
  have hnd : (pC.roots + pD.roots).Nodup := hroots ▸ hm.map neg_injective
  have hdisj := (Multiset.nodup_add.1 hnd).2.2
  have hpC0 : pC ≠ 0 := (spoly_monic r χa).ne_zero
  have hpD0 : pD ≠ 0 := (spoly_monic s χb).ne_zero

  set σ := pC.roots.map Neg.neg with hσ
  have hσm : σ ≤ m := by
    have h1 : pC.roots ≤ m.map Neg.neg := hroots ▸ Multiset.le_add_right _ _
    have h2 := Multiset.map_le_map (f := Neg.neg) h1
    rwa [Multiset.map_map, show (Neg.neg ∘ Neg.neg : ℂ → ℂ) = id from funext neg_neg, Multiset.map_id] at h2
  have hσc : Multiset.card σ = r := by
    rw [hσ, Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, spoly_natDegree]
  have hσn : σ.Nodup := Multiset.nodup_of_le hσm hm
  have hCr : pC.roots = σ.map Neg.neg := by
    rw [hσ, Multiset.map_map, show (Neg.neg ∘ Neg.neg : ℂ → ℂ) = id from funext neg_neg, Multiset.map_id]
  set τ := m - σ with hτ
  have hmστ : m = σ + τ := (add_tsub_cancel_of_le hσm).symm
  have hDr : pD.roots = τ.map Neg.neg := by
    have h1 : pC.roots + pD.roots = pC.roots + τ.map Neg.neg := by
      rw [hroots, hCr, ← Multiset.map_add, ← hmστ]
    exact add_left_cancel h1
  have hτn : τ.Nodup := Multiset.nodup_of_le tsub_le_self hm
  have hmc : Multiset.card m = r + s := by
    have h1 := congrArg natDegree hCD
    rw [natDegree_mul hpC0 hpD0, spoly_natDegree, spoly_natDegree] at h1
    rw [h1, ← IsAlgClosed.card_roots_eq_natDegree, hSr, Multiset.card_map]
  have hτc : Multiset.card τ = s := by
    rw [hτ, Multiset.card_sub hσm, hmc, hσc]; omega

  have hCe : ∀ w, (∑ k ∈ Finset.range (r + 1), w ^ k * χa k) = pC.eval w := fun w => (spoly_eval r χa hχa w).symm
  have hDe : ∀ w, (∑ k ∈ Finset.range (s + 1), w ^ k * χb k) = pD.eval w := fun w => (spoly_eval s χb hχb w).symm
  have hzero : ∀ x ∈ m, (∑ k ∈ Finset.range (r + 1), (-x) ^ k • a k) * (∑ l ∈ Finset.range (s + 1), (-x) ^ l • b l) = 0 := by
    intro x hx
    rw [hrel, Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨x, hx, by ring⟩), zero_smul]
  refine ⟨σ, hσm, hσc, fun u => ⟨?_, ?_⟩⟩
  · refine poly_eq r a ha σ hσn hσc (fun x hx => ?_) u
    have hD : IsUnit (∑ l ∈ Finset.range (s + 1), (-x) ^ l • b l) := by
      refine isUnit_poly s b χb hbb hnb (-x) ?_
      rw [hDe]
      intro h0
      have h1 : -x ∈ pD.roots := (mem_roots hpD0).2 h0
      have h2 : -x ∈ pC.roots := by rw [hCr]; exact Multiset.mem_map.2 ⟨x, hx, rfl⟩
      exact Multiset.disjoint_left.1 hdisj h2 h1
    exact (hD.mul_left_eq_zero).1 (hzero x (Multiset.mem_of_le hσm hx))
  · refine poly_eq s b hb τ hτn hτc (fun x hx => ?_) u
    have hC : IsUnit (∑ k ∈ Finset.range (r + 1), (-x) ^ k • a k) := by
      refine isUnit_poly r a χa haa hna (-x) ?_
      rw [hCe]
      intro h0
      have h1 : -x ∈ pC.roots := (mem_roots hpC0).2 h0
      have h2 : -x ∈ pD.roots := by rw [hDr]; exact Multiset.mem_map.2 ⟨x, hx, rfl⟩
      exact Multiset.disjoint_left.1 hdisj h1 h2
    exact (hC.mul_right_eq_zero).1 (hzero x (Multiset.mem_of_le tsub_le_self hx))

end Piece

section Main

theorem decomp {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] (r s : ℕ)
    (A B : ι → ℕ → Module.End ℂ V) (m : ι → Multiset ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hAW : ∀ i k, ∀ w ∈ W, A i k w ∈ W) (hBW : ∀ i k, ∀ w ∈ W, B i k w ∈ W)
    (hAA : ∀ i k j l, ∀ w ∈ W, A i k (A j l w) = A j l (A i k w))
    (hAB : ∀ i k j l, ∀ w ∈ W, A i k (B j l w) = B j l (A i k w))
    (hBB : ∀ i k j l, ∀ w ∈ W, B i k (B j l w) = B j l (B i k w))
    (hA1 : ∀ i, ∀ w ∈ W, A i r w = w) (hB1 : ∀ i, ∀ w ∈ W, B i s w = w)
    (hm : ∀ i, (m i).Nodup) (v : V) (hv : v ∈ W)
    (hrel : ∀ i (u : ℂ), (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) ((∑ l ∈ Finset.range (s + 1), u ^ l • B i l) v) =
      ((m i).map (u + ·)).prod • v) :
    ∃ (S : Finset (ι → Multiset ℂ)) (x : (ι → Multiset ℂ) → V), (∀ σ ∈ S, x σ ∈ W) ∧ v = ∑ σ ∈ S, x σ ∧
      ∀ σ ∈ S, ∀ i, σ i ≤ m i ∧ Multiset.card (σ i) = r ∧ ∀ u : ℂ,
        (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) (x σ) = ((σ i).map (u + ·)).prod • x σ ∧
        (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) (x σ) = ((m i - σ i).map (u + ·)).prod • x σ := by
  classical

  let A' : ι → ℕ → Module.End ℂ W := fun i k => (A i k).restrict (fun w hw => hAW i k w hw)
  let B' : ι → ℕ → Module.End ℂ W := fun i k => (B i k).restrict (fun w hw => hBW i k w hw)
  have cAA : ∀ i k j l, Commute (A' i k) (A' j l) := fun i k j l =>
    LinearMap.ext fun w => Subtype.ext (hAA i k j l w.1 w.2)
  have cAB : ∀ i k j l, Commute (A' i k) (B' j l) := fun i k j l =>
    LinearMap.ext fun w => Subtype.ext (hAB i k j l w.1 w.2)
  have cBB : ∀ i k j l, Commute (B' i k) (B' j l) := fun i k j l =>
    LinearMap.ext fun w => Subtype.ext (hBB i k j l w.1 w.2)
  let Gs : Set (Module.End ℂ W) :=
    Set.range (fun p : ι × ℕ => A' p.1 p.2) ∪ Set.range (fun p : ι × ℕ => B' p.1 p.2)
  have hGs : ∀ x ∈ Gs, ∀ y ∈ Gs, Commute x y := by
    rintro _ (⟨⟨i, k⟩, rfl⟩ | ⟨⟨i, k⟩, rfl⟩) _ (⟨⟨j, l⟩, rfl⟩ | ⟨⟨j, l⟩, rfl⟩)
    · exact cAA i k j l
    · exact cAB i k j l
    · exact (cAB j l i k).symm
    · exact cBB i k j l
  let R := Algebra.adjoin ℂ Gs
  have hRc : ∀ x ∈ R, ∀ y ∈ R, Commute x y := fun x hx y hy =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb =>
      (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun c hc => hGs b hb c hc).symm
  have hAR : ∀ i k, A' i k ∈ R := fun i k => Algebra.subset_adjoin (Or.inl ⟨(i, k), rfl⟩)
  have hBR : ∀ i k, B' i k ∈ R := fun i k => Algebra.subset_adjoin (Or.inr ⟨(i, k), rfl⟩)
  let Cop : ι → ℂ → Module.End ℂ W := fun i u => ∑ k ∈ Finset.range (r + 1), u ^ k • A' i k
  let Dop : ι → ℂ → Module.End ℂ W := fun i u => ∑ l ∈ Finset.range (s + 1), u ^ l • B' i l
  have hCR : ∀ i u, Cop i u ∈ R := fun i u => R.sum_mem fun k _ => R.smul_mem (hAR i k) _
  have hDR : ∀ i u, Dop i u ∈ R := fun i u => R.sum_mem fun k _ => R.smul_mem (hBR i k) _
  have hCv : ∀ i u (w : W), ((Cop i u w : W) : V) = (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) w := by
    intro i u w
    simp [Cop, A', LinearMap.sum_apply, Submodule.coe_sum]
  have hDv : ∀ i u (w : W), ((Dop i u w : W) : V) = (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) w := by
    intro i u w
    simp [Dop, B', LinearMap.sum_apply, Submodule.coe_sum]

  let v' : W := ⟨v, hv⟩
  let W' : Submodule ℂ W := (Subalgebra.toSubmodule R).map (LinearMap.applyₗ v')
  have hW'm : ∀ w, w ∈ W' ↔ ∃ a ∈ R, a v' = w := fun w => Submodule.mem_map.trans Iff.rfl
  have hW'inv : ∀ x ∈ R, ∀ w ∈ W', x w ∈ W' := by
    intro x hx w hw
    obtain ⟨a, ha, rfl⟩ := (hW'm w).1 hw
    exact (hW'm _).2 ⟨x * a, R.mul_mem hx ha, rfl⟩
  have hrelv : ∀ i u, Cop i u (Dop i u v') = ((m i).map (u + ·)).prod • v' := fun i u =>
    Subtype.ext (by rw [hCv, hDv]; exact hrel i u)
  have hrelW' : ∀ i u, ∀ w ∈ W', Cop i u (Dop i u w) = ((m i).map (u + ·)).prod • w := by
    intro i u w hw
    obtain ⟨a, ha, rfl⟩ := (hW'm w).1 hw
    have e1 : Dop i u (a v') = a (Dop i u v') := by
      rw [← Module.End.mul_apply, (hRc _ (hDR i u) _ ha).eq, Module.End.mul_apply]
    have e2 : Cop i u (a (Dop i u v')) = a (Cop i u (Dop i u v')) := by
      rw [← Module.End.mul_apply, (hRc _ (hCR i u) _ ha).eq, Module.End.mul_apply]
    rw [e1, e2, hrelv, map_smul]

  let f : (ι × ℕ) ⊕ (ι × ℕ) → Module.End ℂ W' := Sum.elim
    (fun p => (A' p.1 p.2).restrict (fun w hw => hW'inv _ (hAR p.1 p.2) w hw))
    (fun p => (B' p.1 p.2).restrict (fun w hw => hW'inv _ (hBR p.1 p.2) w hw))
  have hfR : ∀ j, ∃ x ∈ R, ∀ w : W', (f j w : W) = x w := by
    rintro (⟨i, k⟩ | ⟨i, k⟩)
    · exact ⟨A' i k, hAR i k, fun w => rfl⟩
    · exact ⟨B' i k, hBR i k, fun w => rfl⟩
  have hfc : ∀ j j', Commute (f j) (f j') := by
    intro j j'
    obtain ⟨x, hx, hxe⟩ := hfR j
    obtain ⟨y, hy, hye⟩ := hfR j'
    refine LinearMap.ext fun w => Subtype.ext ?_
    change (f j (f j' w) : W) = (f j' (f j w) : W)
    rw [hxe, hye, hye, hxe, ← Module.End.mul_apply, (hRc x hx y hy).eq, Module.End.mul_apply]
  have hT := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun j j' _ => hfc j j') (fun j => Module.End.iSup_maxGenEigenspace_eq_top _)
  let v'' : W' := ⟨v', (hW'm v').2 ⟨1, R.one_mem, rfl⟩⟩
  have hv'' : v'' ∈ ⨆ χ : (ι × ℕ) ⊕ (ι × ℕ) → ℂ, ⨅ j, (f j).maxGenEigenspace (χ j) := by
    rw [hT]; exact Submodule.mem_top
  obtain ⟨Fs, hFs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hv''
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 hFs
  let P : ((ι × ℕ) ⊕ (ι × ℕ) → ℂ) → Submodule ℂ W' := fun χ => ⨅ j, (f j).maxGenEigenspace (χ j)
  have hPf : ∀ χ j, ∀ x ∈ P χ, f j x ∈ P χ := by
    intro χ j x hx
    simp only [P, Submodule.mem_iInf] at hx ⊢
    intro j'
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hfc j' j) (χ j') (hx j')
  let xx : ((ι × ℕ) ⊕ (ι × ℕ) → ℂ) → V := fun χ => (((μ χ : W') : W) : V)
  have key : ∀ χ : (ι × ℕ) ⊕ (ι × ℕ) → ℂ, ∃ σ : ι → Multiset ℂ, (μ χ : W') ≠ 0 → ∀ i, σ i ≤ m i ∧
      Multiset.card (σ i) = r ∧ ∀ u : ℂ,
        (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) (xx χ) = ((σ i).map (u + ·)).prod • xx χ ∧
        (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) (xx χ) = ((m i - σ i).map (u + ·)).prod • xx χ := by
    intro χ
    by_cases h0 : (μ χ : W') = 0
    · exact ⟨fun _ => 0, fun h => absurd h0 h⟩
    have hpc : ∀ i, ∃ σi : Multiset ℂ, σi ≤ m i ∧ Multiset.card σi = r ∧ ∀ u : ℂ,
        (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) (xx χ) = (σi.map (u + ·)).prod • xx χ ∧
        (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) (xx χ) = ((m i - σi).map (u + ·)).prod • xx χ := by
      intro i
      have : Nontrivial (P χ) := ⟨⟨μ χ, 0, fun h => h0 (congrArg Subtype.val h)⟩⟩
      let a : ℕ → Module.End ℂ (P χ) := fun k => (f (Sum.inl (i, k))).restrict (hPf χ _)
      let b : ℕ → Module.End ℂ (P χ) := fun l => (f (Sum.inr (i, l))).restrict (hPf χ _)
      have hcr : ∀ j j', Commute ((f j).restrict (hPf χ j)) ((f j').restrict (hPf χ j')) := fun j j' =>
        LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun (hfc j j').eq w.1)
      have ha : a r = 1 := LinearMap.ext fun w => Subtype.ext (Subtype.ext (Subtype.ext (hA1 i _ w.1.1.2)))
      have hb : b s = 1 := LinearMap.ext fun w => Subtype.ext (Subtype.ext (Subtype.ext (hB1 i _ w.1.1.2)))
      have hval : ∀ u (w : P χ), ((((∑ k ∈ Finset.range (r + 1), u ^ k • a k) w : P χ) : W') : W) = Cop i u w := by
        intro u w
        simp [a, f, Cop, LinearMap.sum_apply, Submodule.coe_sum]
      have hvalD : ∀ u (w : P χ), ((((∑ l ∈ Finset.range (s + 1), u ^ l • b l) w : P χ) : W') : W) = Dop i u w := by
        intro u w
        simp [b, f, Dop, LinearMap.sum_apply, Submodule.coe_sum]
      have hrelP : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), u ^ k • a k) * (∑ l ∈ Finset.range (s + 1), u ^ l • b l) =
          ((m i).map (u + ·)).prod • (1 : Module.End ℂ (P χ)) := by
        intro u
        refine LinearMap.ext fun w => Subtype.ext (Subtype.ext ?_)
        rw [Module.End.mul_apply, hval]
        have e : ((((∑ l ∈ Finset.range (s + 1), u ^ l • b l) w : P χ) : W')) =
            ⟨Dop i u w, hW'inv _ (hDR i u) _ w.1.2⟩ := Subtype.ext (hvalD u w)
        rw [e]
        change Cop i u (Dop i u w.1.1) = _
        rw [hrelW' i u _ w.1.2]
        rfl
      have hnil : ∀ j, IsNilpotent ((f j).restrict (hPf χ j) - χ j • 1) := by
        intro j
        have h1 := Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (f j) (χ j)
        have hp : Set.MapsTo (f j - algebraMap ℂ (Module.End ℂ W') (χ j)) (P χ) (P χ) := fun x hx => by
          simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
          exact (P χ).sub_mem (hPf χ j x hx) ((P χ).smul_mem _ hx)
        have e : (f j).restrict (hPf χ j) - χ j • 1 = (f j - algebraMap ℂ (Module.End ℂ W') (χ j)).restrict hp := by
          refine LinearMap.ext fun w => Subtype.ext ?_
          rfl
        rw [e]
        exact Module.End.isNilpotent_restrict_of_le (hp := hp) (iInf_le _ j) h1
      obtain ⟨σi, h1, h2, h3⟩ := piece r s a b (fun k l => hcr _ _) (fun k l => hcr _ _) (fun k l => hcr _ _) ha hb
        (m i) (hm i) hrelP (fun k => χ (Sum.inl (i, k))) (fun l => χ (Sum.inr (i, l))) (fun k => hnil _)
        (fun l => hnil _)
      refine ⟨σi, h1, h2, fun u => ⟨?_, ?_⟩⟩
      · have e := congrArg (fun T : Module.End ℂ (P χ) => ((((T (μ χ) : P χ) : W') : W) : V)) (h3 u).1
        rw [hval, hCv] at e
        rw [e]
        rfl
      · have e := congrArg (fun T : Module.End ℂ (P χ) => ((((T (μ χ) : P χ) : W') : W) : V)) (h3 u).2
        rw [hvalD, hDv] at e
        rw [e]
        rfl
    choose σ hσ using hpc
    exact ⟨σ, fun _ i => hσ i⟩
  choose sig hsig using key
  set Fs' := Fs.filter (fun χ => (μ χ : W') ≠ 0) with hFs'
  refine ⟨Fs'.image sig, fun σ => ∑ χ ∈ Fs'.filter (fun χ => sig χ = σ), xx χ, ?_, ?_, ?_⟩
  · intro σ _
    exact W.sum_mem fun χ _ => ((μ χ : W') : W).2
  · rw [Finset.sum_fiberwise_of_maps_to (fun χ hχ => Finset.mem_image_of_mem sig hχ)]
    have e1 : v = (((v'' : W') : W) : V) := rfl
    rw [e1, ← hμ, Submodule.coe_sum, Submodule.coe_sum, hFs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    split_ifs with h
    · rfl
    · rw [not_not] at h
      simp [h]
  · rintro σ hσ i
    obtain ⟨χ₀, hχ₀, rfl⟩ := Finset.mem_image.1 hσ
    obtain ⟨h1, h2, -⟩ := hsig χ₀ (Finset.mem_filter.1 hχ₀).2 i
    refine ⟨h1, h2, fun u => ⟨?_, ?_⟩⟩
    · rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      obtain ⟨hχF, hχe⟩ := Finset.mem_filter.1 hχ
      rw [← hχe]
      exact ((hsig χ (Finset.mem_filter.1 hχF).2 i).2.2 u).1
    · rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      obtain ⟨hχF, hχe⟩ := Finset.mem_filter.1 hχ
      rw [← hχe]
      exact ((hsig χ (Finset.mem_filter.1 hχF).2 i).2.2 u).2

end Main

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra

end
end

section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem rel_expand (G : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), G.1 (unip x * g) = G.1 g)
    (τ : E →+* ℂ) (c : ℂ → ℂ) (hcap : ∀ u, cap τ u G = c u • G) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s)
    (hG : ∀ p, G.1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) (u : ℂ) (p : GA E r × GA E s) :
    ∑ i, (cap τ (u - (s : ℂ) / 2) (b i)).1 p.1 * (cap τ (u + (r : ℂ) / 2) (q i)).1 p.2 =
      c u * ∑ i, (b i).1 p.1 * (q i).1 p.2 := by
  have h1 := CapFactor.cap_levi E r s τ u G hu p
  rw [hcap] at h1
  have hH : ∀ p', (capR r s τ (u - (s : ℂ) / 2) G).1 (lev (Ad E) r s p') =
      ∑ i, (cap τ (u - (s : ℂ) / 2) (b i)).1 p'.1 * (q i).1 p'.2 :=
    fun p' => capR_expand (n := ![r, s]) τ _ G b q hG p'
  have h2 := capS_expand (n := ![r, s]) τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) G)
    (fun i => cap τ (u - (s : ℂ) / 2) (b i)) q hH p
  rw [← hG p]
  change c u * G.1 _ = _ at h1
  rw [h1]
  exact h2.symm

theorem tensL_apply (N : ℕ) (f : ℕ → Module.End ℂ (Sm E r)) (u : ℂ) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) :
    (∑ j ∈ Finset.range N, u ^ j • tensOp (f j) LinearMap.id) (fun p : GA E r × GA E s => ∑ i, (b i).1 p.1 * (q i).1 p.2) =
      fun p => ∑ i, ((∑ j ∈ Finset.range N, u ^ j • f j) (b i)).1 p.1 * (q i).1 p.2 := by
  funext p
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, tensOp_sum, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, LinearMap.id_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tensR_apply (N : ℕ) (f : ℕ → Module.End ℂ (Sm E s)) (u : ℂ) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) :
    (∑ j ∈ Finset.range N, u ^ j • tensOp LinearMap.id (f j)) (fun p : GA E r × GA E s => ∑ i, (b i).1 p.1 * (q i).1 p.2) =
      fun p => ∑ i, (b i).1 p.1 * ((∑ j ∈ Finset.range N, u ^ j • f j) (q i)).1 p.2 := by
  funext p
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, tensOp_sum, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, LinearMap.id_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem fd_tens2 (Z₁ : Submodule ℂ (Sm E r)) (Z₂ : Submodule ℂ (Sm E s)) [FiniteDimensional ℂ Z₁]
    [FiniteDimensional ℂ Z₂] : FiniteDimensional ℂ (tens2 Z₁ Z₂) := by
  classical
  let B₁ := Module.finBasis ℂ Z₁
  let B₂ := Module.finBasis ℂ Z₂
  let f : Fin (Module.finrank ℂ Z₁) × Fin (Module.finrank ℂ Z₂) → (GA E r × GA E s → ℂ) :=
    fun ij m => (B₁ ij.1).1.1 m.1 * (B₂ ij.2).1.1 m.2
  have hle : tens2 Z₁ Z₂ ≤ Submodule.span ℂ (Set.range f) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    have e₁ := B₁.sum_repr ⟨φ₁, h₁⟩
    have e₂ := B₂.sum_repr ⟨φ₂, h₂⟩
    have e : (fun m : GA E r × GA E s => φ₁.1 m.1 * φ₂.1 m.2) =
        ∑ ij : Fin (Module.finrank ℂ Z₁) × Fin (Module.finrank ℂ Z₂), (B₁.repr ⟨φ₁, h₁⟩ ij.1 * B₂.repr ⟨φ₂, h₂⟩ ij.2) • f ij := by
      funext m
      have a₁ := congrArg (fun x : Z₁ => x.1.1 m.1) e₁
      have a₂ := congrArg (fun x : Z₂ => x.1.1 m.2) e₂
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at a₁ a₂
      change φ₁.1 m.1 * φ₂.1 m.2 = _
      rw [← a₁, ← a₂, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩)
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  exact Submodule.finiteDimensional_of_le hle

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end

section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem cap_coeff (a : ℕ) (τ : E →+* ℂ) (d : ℂ) : ∃ f : ℕ → Module.End ℂ (Sm E a), f a = 1 ∧ (∀ k, f k ∈ Zalg E a) ∧
    ∀ u : ℂ, cap τ (u + d) = ∑ k ∈ Finset.range (a + 1), u ^ k • f k := by
  obtain ⟨f, h1, hspan, heq⟩ := QdetCoeff.qdet_shift_coeff (Module.End ℂ (Sm E a)) a (Eop (a := a) τ) (d + ((a : ℂ) - 1) / 2)
  have hc : ∀ u : ℂ, cap τ (u + d) = Formalism.REAL.qdet (Eop (a := a) τ) (u + (d + ((a : ℂ) - 1) / 2)) := fun u => by
    rw [← add_assoc]; rfl
  refine ⟨f, h1, fun k => ?_, fun u => (hc u).trans (heq u)⟩
  have hle : Submodule.span ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet (Eop (a := a) τ) (u + (d + ((a : ℂ) - 1) / 2))) ≤
      Subalgebra.toSubmodule (Zalg E a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, rfl⟩
    change Formalism.REAL.qdet (Eop (a := a) τ) (u + (d + ((a : ℂ) - 1) / 2)) ∈ Zalg E a
    rw [← hc u]
    exact cap_mem_Zalg τ _
  exact hle (hspan k)

def zspan {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) : Submodule ℂ (Sm E a) :=
  Submodule.span ℂ (⋃ i, (fun z : Module.End ℂ (Sm E a) => z (b i)) '' (Zalg E a : Set (Module.End ℂ (Sm E a))))

theorem zspan_fd {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) (hb : ∀ i, IsAutForm (b i)) : FiniteDimensional ℂ (zspan b) := by
  have : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z (b i)) ''
      (Zalg E a : Set (Module.End ℂ (Sm E a))))) := fun i => (hb i).zfin
  rw [zspan, Submodule.span_iUnion]
  infer_instance

theorem zspan_le {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) {L : Submodule ℂ (Sm E a)} (hb : ∀ i, b i ∈ L)
    (hL : ∀ z ∈ Zalg E a, ∀ φ ∈ L, z φ ∈ L) : zspan b ≤ L := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨i, rfl⟩, z, hz, rfl⟩
  exact hL z hz _ (hb i)

theorem mem_zspan {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) (i : Fin k) : b i ∈ zspan b :=
  Submodule.subset_span (Set.mem_iUnion.2 ⟨i, 1, Subalgebra.one_mem _, rfl⟩)

theorem zspan_stable {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∀ φ ∈ zspan b, z φ ∈ zspan b := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, ⟨i, rfl⟩, z', hz', rfl⟩ := hx
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, z * z', Subalgebra.mul_mem _ hz hz', rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx



end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end

section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem decomp_G (G : Sm E (r + s))
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), G.1 (unip x * g) = G.1 g)
    (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hcap : ∀ τ u, cap τ u G = ((mm τ).map (u + ·)).prod • G)
    {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) (hb : ∀ i, IsAutForm (b i)) (hq : ∀ i, IsAutForm (q i))
    (hG : ∀ p, G.1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) :
    ∃ (S : Finset ((E →+* ℂ) → Multiset ℂ)) (x : ((E →+* ℂ) → Multiset ℂ) → (GA E r × GA E s → ℂ)),
      (∀ p, G.1 (lev (Ad E) r s p) = ∑ σ ∈ S, x σ p) ∧
      ∀ σ ∈ S, (∀ τ, σ τ ≤ mm τ ∧ Multiset.card (σ τ) = r) ∧
        (∀ m₂, ∃ θ ∈ zspan b, (∀ y, x σ (y, m₂) = θ.1 y) ∧
          ∀ τ w, cap τ w θ = ((σ τ).map (fun z => w + (s : ℂ) / 2 + z)).prod • θ) ∧
        (∀ m₁, ∃ θ ∈ zspan q, (∀ y, x σ (m₁, y) = θ.1 y) ∧
          ∀ τ w, cap τ w θ = ((mm τ - σ τ).map (fun z => w - (r : ℂ) / 2 + z)).prod • θ) := by
  classical
  have := zspan_fd b hb
  have := zspan_fd q hq
  have := fd_tens2 (zspan b) (zspan q)
  have ca := fun τ : E →+* ℂ => cap_coeff (E := E) r τ (-(s : ℂ) / 2)
  choose fa ha1 haZ haeq using ca
  have cb := fun τ : E →+* ℂ => cap_coeff (E := E) s τ ((r : ℂ) / 2)
  choose fb hb1 hbZ hbeq using cb
  let AA : (E →+* ℂ) → ℕ → Module.End ℂ (GA E r × GA E s → ℂ) := fun τ j => tensOp (fa τ j) LinearMap.id
  let BB : (E →+* ℂ) → ℕ → Module.End ℂ (GA E r × GA E s → ℂ) := fun τ j => tensOp LinearMap.id (fb τ j)
  let v : GA E r × GA E s → ℂ := fun p => ∑ i, (b i).1 p.1 * (q i).1 p.2
  have hAW : ∀ τ j, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ j w ∈ tens2 (zspan b) (zspan q) := by
    intro τ j w hw
    obtain ⟨n, ψ₁, ψ₂, h₁, h₂, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ j) LinearMap.id _ ∈ _
    rw [tensOp_sum]
    exact A.sum_mem (fun i => zspan_stable b (haZ τ j) _ (h₁ i)) (fun i => h₂ i)
  have hBW : ∀ τ j, ∀ w ∈ tens2 (zspan b) (zspan q), BB τ j w ∈ tens2 (zspan b) (zspan q) := by
    intro τ j w hw
    obtain ⟨n, ψ₁, ψ₂, h₁, h₂, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp LinearMap.id (fb τ j) _ ∈ _
    rw [tensOp_sum]
    exact A.sum_mem (fun i => h₁ i) (fun i => zspan_stable q (hbZ τ j) _ (h₂ i))
  have hAA : ∀ τ j τ' l, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ j (AA τ' l w) = AA τ' l (AA τ j w) := by
    intro τ j τ' l w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ j) LinearMap.id (tensOp (fa τ' l) LinearMap.id _) =
      tensOp (fa τ' l) LinearMap.id (tensOp (fa τ j) LinearMap.id _)
    rw [tensOp_sum, tensOp_sum, tensOp_sum, tensOp_sum]
    funext p
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply, (GlobalTheory.LeviGL.ZGood.zalg_commute (haZ τ j) (haZ τ' l)).eq, Module.End.mul_apply]
  have hAB : ∀ τ j τ' l, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ j (BB τ' l w) = BB τ' l (AA τ j w) := by
    intro τ j τ' l w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ j) LinearMap.id (tensOp LinearMap.id (fb τ' l) _) =
      tensOp LinearMap.id (fb τ' l) (tensOp (fa τ j) LinearMap.id _)
    rw [tensOp_sum, tensOp_sum, tensOp_sum, tensOp_sum]
    rfl
  have hBB : ∀ τ j τ' l, ∀ w ∈ tens2 (zspan b) (zspan q), BB τ j (BB τ' l w) = BB τ' l (BB τ j w) := by
    intro τ j τ' l w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp LinearMap.id (fb τ j) (tensOp LinearMap.id (fb τ' l) _) =
      tensOp LinearMap.id (fb τ' l) (tensOp LinearMap.id (fb τ j) _)
    rw [tensOp_sum, tensOp_sum, tensOp_sum, tensOp_sum]
    funext p
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply (fb τ j), (GlobalTheory.LeviGL.ZGood.zalg_commute (hbZ τ j) (hbZ τ' l)).eq, Module.End.mul_apply]
  have hA1 : ∀ τ, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ r w = w := by
    intro τ w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ r) LinearMap.id _ = _
    rw [tensOp_sum, ha1 τ]
    rfl
  have hB1 : ∀ τ, ∀ w ∈ tens2 (zspan b) (zspan q), BB τ s w = w := by
    intro τ w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp LinearMap.id (fb τ s) _ = _
    rw [tensOp_sum, hb1 τ]
    rfl
  have hv : v ∈ tens2 (zspan b) (zspan q) := A.sum_mem (fun i => mem_zspan b i) (fun i => mem_zspan q i)
  have hrel : ∀ τ (u : ℂ), (∑ j ∈ Finset.range (r + 1), u ^ j • AA τ j) ((∑ l ∈ Finset.range (s + 1), u ^ l • BB τ l) v) =
      ((mm τ).map (u + ·)).prod • v := by
    intro τ u
    change (∑ j ∈ Finset.range (r + 1), u ^ j • tensOp (fa τ j) LinearMap.id)
      ((∑ l ∈ Finset.range (s + 1), u ^ l • tensOp LinearMap.id (fb τ l)) v) = _
    rw [tensR_apply, ← hbeq τ u, tensL_apply, ← haeq τ u]
    funext p
    have e : u + -(s : ℂ) / 2 = u - (s : ℂ) / 2 := by ring
    rw [e, rel_expand G hu τ (fun u => ((mm τ).map (u + ·)).prod) (hcap τ) b q hG u p]
    rfl
  obtain ⟨S, x, hxW, hsum, hprop⟩ := BlockAlgebra.decomp r s AA BB mm (tens2 (zspan b) (zspan q)) hAW hBW hAA hAB hBB
    hA1 hB1 hmm v hv hrel
  refine ⟨S, x, fun p => ?_, fun σ hσ => ⟨fun τ => ⟨(hprop σ hσ τ).1, (hprop σ hσ τ).2.1⟩, fun m₂ => ?_, fun m₁ => ?_⟩⟩
  · rw [hG]
    change v p = _
    rw [hsum, Finset.sum_apply]
  · obtain ⟨n, ψ₁, ψ₂, h₁, -, hx⟩ := tensor_pair_finite_sum (hxW σ hσ)
    refine ⟨∑ i, (ψ₂ i).1 m₂ • ψ₁ i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i),
      fun y => by rw [hx]; simp [Finset.sum_apply, mul_comm], fun τ w => ?_⟩
    have key := ((hprop σ hσ τ).2.2 (w + (s : ℂ) / 2)).1
    change (∑ j ∈ Finset.range (r + 1), (w + (s : ℂ) / 2) ^ j • tensOp (fa τ j) LinearMap.id) (x σ) = _ at key
    rw [hx, tensL_apply, ← haeq τ] at key
    have e : w + (s : ℂ) / 2 + -(s : ℂ) / 2 = w := by ring
    rw [e] at key
    refine Subtype.ext (funext fun y => ?_)
    have k2 := congrFun key (y, m₂)
    simp only [Pi.smul_apply, smul_eq_mul] at k2
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    simp only [mul_comm ((ψ₂ _).1 m₂)] at k2 ⊢
    rw [k2, Finset.mul_sum]
  · obtain ⟨n, ψ₁, ψ₂, -, h₂, hx⟩ := tensor_pair_finite_sum (hxW σ hσ)
    refine ⟨∑ i, (ψ₁ i).1 m₁ • ψ₂ i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i),
      fun y => by rw [hx]; simp [Finset.sum_apply], fun τ w => ?_⟩
    have key := ((hprop σ hσ τ).2.2 (w - (r : ℂ) / 2)).2
    change (∑ j ∈ Finset.range (s + 1), (w - (r : ℂ) / 2) ^ j • tensOp LinearMap.id (fb τ j)) (x σ) = _ at key
    rw [hx, tensR_apply, ← hbeq τ] at key
    have e : w - (r : ℂ) / 2 + (r : ℂ) / 2 = w := by ring
    rw [e] at key
    refine Subtype.ext (funext fun y => ?_)
    have k2 := congrFun key (m₁, y)
    simp only [Pi.smul_apply, smul_eq_mul] at k2
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [k2, Finset.mul_sum]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem zalg_comm {N : ℕ} {I : Submodule ℂ (Sm E N)} (hI : ∀ X, ∀ φ ∈ I, lie E N X φ ∈ I)
    (f : Sm E N →ₗ[ℂ] Sm E N) (hf : ∀ o, ∀ φ ∈ I, f (act o φ) = act o (f φ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Zalg E N) : ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ) := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E N)) :=
    { carrier := {z | ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ)}
      mul_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hy φ hφ
        obtain ⟨h2, e2⟩ := hx _ h1
        exact ⟨h2, by simp only [Module.End.mul_apply]; rw [e2, e1]⟩
      add_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hx φ hφ
        obtain ⟨h2, e2⟩ := hy φ hφ
        exact ⟨add_mem h1 h2, by simp only [LinearMap.add_apply, map_add, e1, e2]⟩
      algebraMap_mem' := fun c φ hφ => ⟨by simpa only [Module.algebraMap_end_apply] using I.smul_mem c hφ,
        by simp only [Module.algebraMap_end_apply, map_smul]⟩ }
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap τ u ∈ S := fun τ u φ hφ =>
    ⟨Zalg_stable hI (cap_mem_Zalg τ u) φ hφ, GlobalTheory.SpehInfChar.cap_comm_quot hI f hf τ u φ hφ⟩
  have hle : Zalg E N ≤ S := Algebra.adjoin_le (by rintro _ ⟨τ, u, rfl⟩; exact hcap τ u)
  exact hle hz

variable {r s : ℕ}

theorem expand {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
    (hT : IsSliceMap U c T) : ∀ ψ ∈ U, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
      ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s), (∀ i, b i ∈ Submodule.span ℂ (lsF r s (T ψ) k g)) ∧
        (∀ i, q i ∈ rsF r s (T ψ) k g) ∧
        ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m * yp k g) = ∑ i, (b i).1 m.1 * (q i).1 m.2 := by
  intro ψ hψ k g
  have hAψ : IsAutForm ψ := hU.2 ψ hψ
  have hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U := fun X φ hφ => hU.1 (.lie X) φ hφ

  let L := GlobalTheory.DiscClosure.stabSub ψ
  have hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) := hAψ.level
  have hLv : ∀ h ∈ L, finRep E (r + s) h (T ψ) = T ψ := fun h hh => by
    have e := hT.equiv (.fin h) ψ hψ
    have hh' : finRep E (r + s) h ψ = ψ := hh
    change T (finRep E (r + s) h ψ) = finRep E (r + s) h (T ψ) at e
    rw [← e, hh']

  let S := GlobalTheory.CuspRep.LocEx.orbSpan (T ψ)
  have : FiniteDimensional ℂ S := by
    have := hAψ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ ψ)).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨κ, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨κ, rfl⟩, hT.equiv (.cpt κ) ψ hψ⟩
  let ρ := GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T ψ))
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := GlobalTheory.CuspRep.LocEx.isContRep_sub S _
  have hC : ∀ g' : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T ψ)).1 g') ∈
      GlobalTheory.Published.AutFin.coeffSpan ρ := fun g' =>
    GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T ψ, Submodule.subset_span ⟨1, by simp⟩⟩ g'

  have := hAψ.zfin
  let J : Set (Module.End ℂ (Sm E (r + s))) := {z | z ∈ Zalg E (r + s) ∧ z ψ = 0}
  have hJ : Cofin J := PositivityTheory.Rg.Rs.JFinTr.cofin_ann ψ
  have hJZ : J ⊆ Zalg E (r + s) := fun z hz => hz.1
  have hZ : ∀ z ∈ J, z (T ψ) = 0 := by
    rintro z ⟨hz, hzψ⟩
    rw [← (zalg_comm hI T hT.equiv hz ψ hψ).2, hzψ, map_zero]
  obtain ⟨J₁, -, c₁, -, k₁, -⟩ := centre J hJ

  let L₁ := Slice1.levelOne s L g
  let ρ₁ := ρ.comp (Slice1.levK E r s)
  have := PositivityTheory.Rg.HF.GL.genFin E r L₁ (Slice1.isOpen_levelOne hLo g) S ρ₁
    (fun ℓ w => (hρ ℓ w).comp Slice1.continuous_levK) J₁ c₁
  let S₁ := Submodule.span ℂ (lsF r s (T ψ) k g) ⊓ Submodule.span ℂ (genSpace L₁ ρ₁ J₁)
  have : FiniteDimensional ℂ S₁ := Submodule.finiteDimensional_of_le inf_le_right
  let U' := S₁.map (Sm E r).subtype
  obtain ⟨P, a, ha⟩ := SliceTensor.interp U'
  let f : GA E r × GA E s → ℂ := fun m => (T ψ).1 (lev (Ad E) r s m * yp k g)
  have hleft : ∀ m₂, (fun m₁ => f (m₁, m₂)) ∈ U' := by
    intro m₂
    obtain ⟨ψ₁, hψA, hψ₁, -⟩ := hT.left ψ hψ k g m₂
    have hmem : ψ₁ ∈ genSpace L₁ ρ₁ J₁ := by
      refine SliceTensor.slice_mem ρ hJZ k₁ (T ψ) (hT.unipInv ψ hψ) hLv hC hZ g k m₂ ψ₁ hψA fun m₁ => ?_
      rw [hψ₁, infGL_comm, mul_assoc]
    have hls : ψ₁ ∈ lsF r s (T ψ) k g := ⟨m₂, fun m₁ => hψ₁ m₁⟩
    exact ⟨ψ₁, ⟨Submodule.subset_span hls, Submodule.subset_span hmem⟩, funext fun m₁ => hψ₁ m₁⟩
  have hb : ∀ κ : P, ∃ b ∈ Submodule.span ℂ (lsF r s (T ψ) k g), b.1 = (a κ : GA E r → ℂ) := by
    intro κ
    obtain ⟨b, hb, e⟩ := (a κ).2
    exact ⟨b, hb.1, e⟩
  choose b hbm hbe using hb
  have hright : ∀ κ : P, ∃ ψ₂ ∈ rsF r s (T ψ) k g, ∀ m₂, ψ₂.1 m₂ = f (κ.1, m₂) := by
    intro κ
    obtain ⟨ψ₂, -, e, -⟩ := hT.right ψ hψ k g κ.1
    exact ⟨ψ₂, ⟨κ.1, fun m₂ => e m₂⟩, e⟩
  choose q hqm hqe using hright
  have hf : ∀ m : GA E r × GA E s, f m = ∑ κ : P, (b κ).1 m.1 * (q κ).1 m.2 := by
    intro m
    have e := congrFun (ha _ (hleft m.2)) m.1
    rw [Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun κ _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, hbe, hqe]
    ring
  let eP := (Fintype.equivFin P).symm
  refine ⟨Fintype.card P, fun i => b (eP i), fun i => q (eP i), fun i => hbm _, fun i => hqm _, fun m => ?_⟩
  rw [show (T ψ).1 (lev (Ad E) r s m * yp k g) = f m from rfl, hf m]
  exact (Equiv.sum_comp eP (fun κ => (b κ).1 m.1 * (q κ).1 m.2)).symm

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs GlobalTheory.BlockCap
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem act_fin_apply {a : ℕ} (h : GL (Fin a) (Af E)) (F : Sm E a) (x : GA E a) :
    (act (.fin h) F).1 x = F.1 (x * finGL E a h) := rfl

theorem act_cpt_apply {a : ℕ} (k : Kinf E a) (F : Sm E a) (x : GA E a) :
    (act (.cpt k) F).1 x = F.1 (x * infGL E a (Unitary.toUnits k)) := rfl

variable {r s : ℕ}

theorem yp_one : yp (E := E) (a := r + s) 1 1 = 1 := by
  simp [yp]

theorem base_one {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
    (hT : IsSliceMap U c T) {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∃ ψ' ∈ U, ∀ x, (T ψ').1 x = (T ψ).1 (x * yp k g) := by
  refine ⟨act (.cpt k) (act (.fin g) ψ), hU.1 _ _ (hU.1 _ _ hψ), fun x => ?_⟩
  rw [hT.equiv _ _ (hU.1 _ _ hψ), hT.equiv _ _ hψ]
  exact InducedTensorMap.A.act_cf k g (T ψ) x

theorem mem_LS_of {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (ℓ : Sm E r) (m₂ : GA E s) (h : ∀ m₁, ℓ.1 m₁ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) : ℓ ∈ LS U T :=
  Submodule.subset_span ⟨ψ, hψ, 1, 1, m₂, fun m₁ => by rw [h, yp_one, mul_one]⟩

theorem mem_RS_of {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (ℓ : Sm E s) (m₁ : GA E r) (h : ∀ m₂, ℓ.1 m₂ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) : ℓ ∈ RS U T :=
  Submodule.subset_span ⟨ψ, hψ, 1, 1, m₁, fun m₂ => by rw [h, yp_one, mul_one]⟩

omit [IsCMField E] in
theorem upd0 (m₁ y : GA E r) (m₂ : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, m₂)) 0 y = CapFactor.levPair (n := ![r, s]) (y, m₂) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

omit [IsCMField E] in
theorem upd1 (m₁ : GA E r) (m₂ y : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, m₂)) 1 y = CapFactor.levPair (n := ![r, s]) (m₁, y) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

section Step

variable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
  (hT : IsSliceMap U c T)
include hU hT

theorem act_left {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (ℓ : Sm E r) (m₂ : GA E s)
    (h : ∀ m₁, ℓ.1 m₁ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) (o : Op E r) : act o ℓ ∈ LS U T := by
  cases o with
  | fin h' =>
    refine mem_LS_of (hU.1 (.fin (lev (Af E) r s (h', 1))) ψ hψ) _ m₂ fun m₁ => ?_
    have e : lev (Ad E) r s (finGL E r h', 1) = finGL E (r + s) (lev (Af E) r s (h', 1)) := by
      rw [← Slice1.lev_finGL, map_one]
    rw [act_fin_apply, h, hT.equiv _ _ hψ, act_fin_apply, Slice1.lev_mul_one, e]
  | cpt κ =>
    refine mem_LS_of (hU.1 (.cpt (Slice1.levK E r s κ)) ψ hψ) _ m₂ fun m₁ => ?_
    rw [act_cpt_apply, h, hT.equiv _ _ hψ, act_cpt_apply, Slice1.lev_mul_one, Slice1.infGL_levK]
  | lie X =>
    let n : Fin 2 → ℕ := ![r, s]
    have h2 : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
    refine mem_LS_of (hU.1 (.lie (blockCLM (stdBlocks n h2) 0 X)) ψ hψ) _ m₂ fun m₁ => ?_
    have key := LinearMap.congr_fun
      (restrLin_lie (E := E) (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 X) (T ψ)
    have hℓ : ℓ = restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 (T ψ) :=
      Subtype.ext (funext fun y => by
        rw [h y]
        change _ = (T ψ).1 (leviEmb (Ad E) (stdBlocks n h2)
          (Function.update (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 y))
        rw [upd0, ← CapFactor.lev_eq_leviEmb]
        rfl)
    have key2 : (restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0
        (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ))).1 m₁ = (lie E r X ℓ).1 m₁ := by
      rw [hℓ]
      exact congrArg (fun φ : Sm E (n 0) => φ.1 m₁) key
    rw [hT.equiv _ _ hψ]
    change (lie E r X ℓ).1 m₁ = (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ)).1 (lev (Ad E) r s (m₁, m₂))
    rw [← key2]
    change (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ)).1 (leviEmb (Ad E) (stdBlocks n h2)
      (Function.update (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 m₁)) = _
    rw [upd0, ← CapFactor.lev_eq_leviEmb]
    rfl

theorem act_right {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (ℓ : Sm E s) (m₁ : GA E r)
    (h : ∀ m₂, ℓ.1 m₂ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) (o : Op E s) : act o ℓ ∈ RS U T := by
  cases o with
  | fin h' =>
    refine mem_RS_of (hU.1 (.fin (lev (Af E) r s (1, h'))) ψ hψ) _ m₁ fun m₂ => ?_
    rw [act_fin_apply, h, hT.equiv _ _ hψ, act_fin_apply, Slice2.lev_mul_right, Slice2.lev_finGL_one]
  | cpt κ =>
    refine mem_RS_of (hU.1 (.cpt (Slice2.levK E r s κ)) ψ hψ) _ m₁ fun m₂ => ?_
    rw [act_cpt_apply, h, hT.equiv _ _ hψ, act_cpt_apply, Slice2.lev_mul_right, Slice2.lev_infGL_one,
      Slice2.toUnits_levK]
  | lie X =>
    let n : Fin 2 → ℕ := ![r, s]
    have h2 : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
    refine mem_RS_of (hU.1 (.lie (blockCLM (stdBlocks n h2) 1 X)) ψ hψ) _ m₁ fun m₂ => ?_
    have key := LinearMap.congr_fun
      (restrLin_lie (E := E) (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 X) (T ψ)
    have hℓ : ℓ = restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 (T ψ) :=
      Subtype.ext (funext fun y => by
        rw [h y]
        change _ = (T ψ).1 (leviEmb (Ad E) (stdBlocks n h2)
          (Function.update (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 y))
        rw [upd1, ← CapFactor.lev_eq_leviEmb]
        rfl)
    have key2 : (restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1
        (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ))).1 m₂ = (lie E s X ℓ).1 m₂ := by
      rw [hℓ]
      exact congrArg (fun φ : Sm E (n 1) => φ.1 m₂) key
    rw [hT.equiv _ _ hψ]
    change (lie E s X ℓ).1 m₂ = (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ)).1 (lev (Ad E) r s (m₁, m₂))
    rw [← key2]
    change (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ)).1 (leviEmb (Ad E) (stdBlocks n h2)
      (Function.update (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 m₂)) = _
    rw [upd1, ← CapFactor.lev_eq_leviEmb]
    rfl

theorem LS_stable : IsStable (LS U T) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ', hψ', e⟩ := base_one hU hT hψ k g
    exact act_left hU hT hψ' x m₂ (fun m₁ => by rw [hx, ← e]) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem RS_stable : IsStable (RS U T) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ', hψ', e⟩ := base_one hU hT hψ k g
    exact act_right hU hT hψ' x m₁ (fun m₂ => by rw [hx, ← e]) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

omit hU in

theorem LS_aut : ∀ φ ∈ LS U T, IsAutForm φ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ₁, hA, h1, -⟩ := hT.left ψ hψ k g m₂
    have : x = ψ₁ := Subtype.ext (funext fun m₁ => (hx m₁).trans (h1 m₁).symm)
    exact this ▸ hA
  | zero => exact GlobalTheory.HCF.FormsSub.isAutForm_zero
  | add x y _ _ hx hy => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hx hy
  | smul a x _ hx => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul a hx

omit hU in

theorem RS_aut : ∀ φ ∈ RS U T, IsAutForm φ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ₂, hA, h1, -⟩ := hT.right ψ hψ k g m₁
    have : x = ψ₂ := Subtype.ext (funext fun m₂ => (hx m₂).trans (h1 m₂).symm)
    exact this ▸ hA
  | zero => exact GlobalTheory.HCF.FormsSub.isAutForm_zero
  | add x y _ _ hx hy => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hx hy
  | smul a x _ hx => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul a hx

theorem memInd2 : ∀ ψ ∈ U, MemInd2 (LS U T) (RS U T) (T ψ) := by
  intro ψ hψ
  refine ⟨hT.unipInv ψ hψ, fun k g => ?_⟩
  obtain ⟨n, b, q, hb, hq, he⟩ := expand hU hT ψ hψ k g
  have e : (fun m => (T ψ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) =
      fun m => ∑ i, (b i).1 m.1 * (q i).1 m.2 := funext he
  rw [e]
  exact ParabolicProjection.sum_mem_tens2 (fun i => Submodule.span_le.2 (lsF_sub_LS hψ k g) (hb i))
    (fun i => rsF_sub_RS hψ k g (hq i))

end Step

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

end
end

section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Eig {a : ℕ} (L : Submodule ℂ (Sm E a)) (σ : (E →+* ℂ) → Multiset ℂ) (sh : ℂ) : Submodule ℂ (Sm E a) where
  carrier := {φ | φ ∈ L ∧ ∀ τ w, cap τ w φ = ((σ τ).map (fun z => w + sh + z)).prod • φ}
  add_mem' := fun {φ ψ} hφ hψ => ⟨L.add_mem hφ.1 hψ.1, fun τ w => by rw [map_add, hφ.2, hψ.2, smul_add]⟩
  zero_mem' := ⟨L.zero_mem, fun τ w => by rw [map_zero, smul_zero]⟩
  smul_mem' := fun c φ hφ => ⟨L.smul_mem c hφ.1, fun τ w => by rw [map_smul, hφ.2, smul_comm]⟩

def adm (mm : (E →+* ℂ) → Multiset ℂ) (n : ℕ) : Finset ((E →+* ℂ) → Multiset ℂ) := by
  classical
  exact Fintype.piFinset fun τ => ((mm τ).powerset.filter fun σ => Multiset.card σ = n).toFinset

theorem mem_adm {mm : (E →+* ℂ) → Multiset ℂ} {n : ℕ} {σ : (E →+* ℂ) → Multiset ℂ} :
    σ ∈ adm mm n ↔ ∀ τ, σ τ ≤ mm τ ∧ Multiset.card (σ τ) = n := by
  classical
  unfold adm
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun τ => ?_
  rw [Multiset.mem_toFinset, Multiset.mem_filter, Multiset.mem_powerset]

variable {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem LS_zalg (hU : IsAutSt U) (hT : IsSliceMap U c T) : ∀ z ∈ Zalg E r, ∀ φ ∈ LS U T, z φ ∈ LS U T :=
  fun _ hz φ hφ => Zalg_stable (fun X => BlockSlices.LS_stable hU hT (.lie X)) hz φ hφ

theorem RS_zalg (hU : IsAutSt U) (hT : IsSliceMap U c T) : ∀ z ∈ Zalg E s, ∀ φ ∈ RS U T, z φ ∈ RS U T :=
  fun _ hz φ hφ => Zalg_stable (fun X => BlockSlices.RS_stable hU hT (.lie X)) hz φ hφ

theorem data_one (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) {ψ : Sm E (r + s)} (hψ : ψ ∈ U) :
    (∀ τ u, cap τ u (T ψ) = ((mm τ).map (u + ·)).prod • T ψ) ∧
    ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s), (∀ i, b i ∈ LS U T) ∧ (∀ i, q i ∈ RS U T) ∧
      ∀ p, (T ψ).1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2 := by
  refine ⟨fun τ u => ?_, ?_⟩
  · have hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U := fun X φ hφ => hU.1 (.lie X) φ hφ
    rw [← (BlockSlices.zalg_comm hI T hT.equiv (cap_mem_Zalg τ u) ψ hψ).2, (hinf τ).2 u ψ hψ, map_smul]
  · obtain ⟨n, b, q, hb, hq, he⟩ := BlockSlices.expand hU hT ψ hψ 1 1
    refine ⟨n, b, q, fun i => ?_, fun i => rsF_sub_RS hψ 1 1 (hq i), fun p => ?_⟩
    · exact (Submodule.span_le.2 (lsF_sub_LS hψ 1 1)) (hb i)
    · rw [← he p, BlockSlices.yp_one, mul_one]

theorem LS_le_iSup (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) :
    LS U T ≤ ⨆ σ ∈ adm mm r, Eig (LS U T) σ ((s : ℂ) / 2) := by
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₂, hℓ⟩
  obtain ⟨ψ', hψ', e⟩ := BlockSlices.base_one hU hT hψ k g
  obtain ⟨hcap, n, b, q, hb, hq, hG⟩ := data_one hU hT mm hinf hψ'
  obtain ⟨S, x, hsum, hS⟩ := decomp_G (T ψ') (hT.unipInv ψ' hψ') mm hmm hcap b q
    (fun i => BlockSlices.LS_aut hT _ (hb i)) (fun i => BlockSlices.RS_aut hT _ (hq i)) hG
  have hz := zspan_le b hb (LS_zalg hU hT)
  choose θ hθ hθx hθe using fun σ (hσ : σ ∈ S) => (hS σ hσ).2.1 m₂
  have hℓ' : ℓ = ∑ σ ∈ S.attach, θ σ.1 σ.2 := by
    refine Subtype.ext (funext fun m₁ => ?_)
    rw [hℓ, ← e, hsum, Submodule.coe_sum, Finset.sum_apply, ← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun σ _ => hθx σ.1 σ.2 m₁
  rw [SetLike.mem_coe, hℓ']
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hadm : σ.1 ∈ adm mm r := mem_adm.2 (hS σ.1 σ.2).1
  exact Submodule.mem_iSup_of_mem σ.1 (Submodule.mem_iSup_of_mem hadm ⟨hz (hθ σ.1 σ.2), hθe σ.1 σ.2⟩)

theorem RS_le_iSup (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) :
    RS U T ≤ ⨆ ρ ∈ adm mm s, Eig (RS U T) ρ (-(r : ℂ) / 2) := by
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₁, hℓ⟩
  obtain ⟨ψ', hψ', e⟩ := BlockSlices.base_one hU hT hψ k g
  obtain ⟨hcap, n, b, q, hb, hq, hG⟩ := data_one hU hT mm hinf hψ'
  obtain ⟨S, x, hsum, hS⟩ := decomp_G (T ψ') (hT.unipInv ψ' hψ') mm hmm hcap b q
    (fun i => BlockSlices.LS_aut hT _ (hb i)) (fun i => BlockSlices.RS_aut hT _ (hq i)) hG
  have hz := zspan_le q hq (RS_zalg hU hT)
  choose θ hθ hθx hθe using fun σ (hσ : σ ∈ S) => (hS σ hσ).2.2 m₁
  have hℓ' : ℓ = ∑ σ ∈ S.attach, θ σ.1 σ.2 := by
    refine Subtype.ext (funext fun m₂ => ?_)
    rw [hℓ, ← e, hsum, Submodule.coe_sum, Finset.sum_apply, ← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun σ _ => hθx σ.1 σ.2 m₂
  rw [SetLike.mem_coe, hℓ']
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hadm : (fun τ => mm τ - σ.1 τ) ∈ adm mm s := mem_adm.2 fun τ => by
    refine ⟨Multiset.sub_le_self _ _, ?_⟩
    rw [Multiset.card_sub ((hS σ.1 σ.2).1 τ).1, (hinf τ).1, ((hS σ.1 σ.2).1 τ).2]
    omega
  refine Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hadm ⟨hz (hθ σ.1 σ.2), fun τ w => ?_⟩)
  rw [hθe σ.1 σ.2 τ w]
  congr 3
  funext z
  ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end
