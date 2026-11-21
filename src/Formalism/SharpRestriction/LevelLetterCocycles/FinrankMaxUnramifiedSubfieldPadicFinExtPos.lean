import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse
import Formalism.PadicSubsetSums.StableGradedCounts.FrobeniusDifferenceDividedPower
import Development.AutomorphicArithmetic.CyclotomicBounds.ImageMemOfGens
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots

section
noncomputable section

namespace Formalism.MainNotions.EmbeddingTypeJumps

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open scoped Pointwise

variable (D : D7)

section Sqrt

open Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

theorem sqrt_neg_mem (M : IntermediateField ℚ_[l] (Om l)) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3)
    (ζ : Om l) (hζ : IsPrimitiveRoot ζ p) (hM : ζ ∈ M) (y : Om l) (hy : y ^ 2 = -(p : Om l)) :
    y ∈ M := by
  obtain ⟨z, hz⟩ := Formalism.IrreducibleCountingLemmas.WindowSums.sqrt_neg_in_cyclotomic_field p hp hp4 ↥M ⟨ζ, hM⟩
    (IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ)
  have hz' : -(p : Om l) = (z : Om l) * z := by
    have := congrArg (Subtype.val : ↥M → Om l) hz
    simpa using this
  have h0 : (y - z) * (y + z) = 0 := by linear_combination hy + hz'
  rcases mul_eq_zero.mp h0 with h | h
  · rw [sub_eq_zero.mp h]; exact z.2
  · rw [eq_neg_of_add_eq_zero_left h]; exact M.neg_mem z.2

theorem exists_prim (p : ℕ) (hp : p.Prime) : ∃ ζ : Om l, IsPrimitiveRoot ζ p := by
  have : NeZero (p : Om l) := ⟨by exact_mod_cast hp.ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) p

theorem sqrt_mem_Kur (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (hpl : p ≠ l) (y : Om l)
    (hy : y ^ 2 = -(p : Om l)) : y ∈ MaximalUnramifiedExtension l := by
  obtain ⟨ζ, hζ⟩ := exists_prim (l := l) p hp
  refine sqrt_neg_mem (MaximalUnramifiedExtension l) p hp hp4 ζ hζ (IntermediateField.subset_adjoin _ _ ?_) y hy
  refine ⟨p, hp.pos, ?_, hζ.pow_eq_one⟩
  intro h
  exact hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hp).mp h).symm

theorem sqrt_mem_Ks (hl4 : l % 4 = 3) (K : FinExt l) (y : Om l) (hy : y ^ 2 = -(l : Om l)) :
    y ∈ Ks K 1 := by
  obtain ⟨ζ, hζ⟩ := exists_prim (l := l) l Fact.out
  refine sqrt_neg_mem (Ks K 1) l Fact.out hl4 ζ hζ ?_ y hy
  apply (le_sup_right : _ ≤ Ks K 1)
  apply IntermediateField.subset_adjoin
  show ζ ^ (l ^ 1) = 1
  rw [pow_one]; exact hζ.pow_eq_one

end Sqrt

section Local

open Formalism.BasicNotions.Loc Polynomial UpperTheory.InertGen

variable {l : ℕ} [Fact l.Prime] {R : Ranks} (H : Host R) (J : H.E →+* Om l)

theorem theta_mem_Kur : J (thetaAt H.toHostRaw l) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨z, hz, hθ⟩ := image_inertField H.toHostRaw J (l := l)
  have hN := H.toHostRaw.condN_ne_zero
  have hzK : z ∈ (MaximalUnramifiedExtension l).toSubfield := IntermediateField.subset_adjoin _ _
    ⟨_, Nat.ordCompl_pos l hN, Nat.not_dvd_ordCompl Fact.out hN, hz⟩
  exact (Subfield.closure_le.2 (Set.singleton_subset_iff.2 hzK) : Subfield.closure {z} ≤ (MaximalUnramifiedExtension l).toSubfield)
    (hθ _ (thetaAt_mem _ l))

theorem adjoin_gen_top {p : ℕ} (hp : p.Prime) (hpS : ¬ p ∣ H.QS) :
    IntermediateField.adjoin ℚ ({thetaAt H.toHostRaw p, H.sqq, H.sqd} : Set H.E) = ⊤ :=
  adjoin_thetaAt_top H hp hpS

theorem image_le (hlS : ¬ l ∣ H.QS) (M : IntermediateField ℚ_[l] (Om l)) (h1 : J (thetaAt H.toHostRaw l) ∈ M)
    (h2 : J (H.sqq) ∈ M) (h3 : J (H.sqd) ∈ M) (x : H.E) : J x ∈ M := by
  have hx : x ∈ IntermediateField.adjoin ℚ ({thetaAt H.toHostRaw l, H.sqq, H.sqd} : Set H.E) := by
    rw [adjoin_gen_top H Fact.out hlS]; trivial
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | rfl | rfl
    exacts [h1, h2, h3]
  | algebraMap r =>
    rw [eq_ratCast, map_ratCast]
    exact SubfieldClass.ratCast_mem M r
  | add a b _ _ ha hb => rw [map_add]; exact M.add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact M.inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact M.mul_mem ha hb

theorem local_pre (hl : l = H.q ∨ l = H.d) (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) :
    (∃ y : Om l, y ^ 2 = -(l : Om l) ∧
      Kw.1 = K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}) ∧ Kw.1 ≤ Ks Kw 1 := by
  have hh := H.hyp
  have hqd := H.hypOdd
  have ha : (J (H.sqq)) ^ 2 = -(H.q : Om l) := by
    rw [← map_pow, H.sqq_sq]; simp
  have hb : (J (H.sqd)) ^ 2 = -(H.d : Om l) := by
    rw [← map_pow, H.sqd_sq]; simp
  have hlS : ¬ l ∣ H.QS := by rcases hl with h | h <;> rw [h]; exacts [H.q_not_dvd_QS, H.d_not_dvd_QS]
  have hl4 : l % 4 = 3 := by
    have h1 := hh.2.2.1
    have h2 := hh.2.2.2.1
    rcases hl with h | h <;> rw [h] <;> omega
  have hθ := theta_mem_Kur H J

  have key : ∀ y z : Om l, J (thetaAt H.toHostRaw l) ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} →
      J (H.sqq) ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} →
      J (H.sqd) ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} → y ∈ Kw.1 → z = y →
      Kw.1 = K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} := by
    intro y z h1 h2 h3 hy _
    have hle : K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} ≤ Kw.1 :=
      sup_le inf_le_left (IntermediateField.adjoin_le_iff.mpr (by simpa using hy))
    have : FiniteDimensional ℚ_[l] ↥Kw.1 := Kw.2
    have hfd : FiniteDimensional ℚ_[l] ↥(K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}) :=
      FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
        (IntermediateField.inclusion hle).injective
    have hcl : IsClosed ((K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} :
        IntermediateField ℚ_[l] (Om l)) : Set (Om l)) :=
      Submodule.closed_of_finiteDimensional
        (K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}).toSubalgebra.toSubmodule
    refine le_antisymm (fun x hx => ?_) hle
    refine closure_minimal ?_ hcl (hdense hx)
    rintro _ ⟨x, rfl⟩
    exact image_le H J hlS _ h1 h2 h3 x
  have hK0 : ∀ x : H.E, J x ∈ MaximalUnramifiedExtension l → ∀ y : Om l,
      J x ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} :=
    fun x hx y => (le_sup_left : K0 Kw ≤ _) ⟨hE x, hx⟩
  have hself : ∀ y : Om l, y ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} :=
    fun y => (le_sup_right : IntermediateField.adjoin ℚ_[l] {y} ≤ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  have main : ∃ y : Om l, y ^ 2 = -(l : Om l) ∧
      Kw.1 = K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} := by
    rcases hl with h | h
    · refine ⟨J (H.sqq), by rw [ha]; exact congrArg (fun n : ℕ => -(n : Om l)) h.symm, key _ _ (hK0 _ hθ _) (hself _) (hK0 _ ?_ _) (hE _) rfl⟩
      exact sqrt_mem_Kur H.d hh.2.1 (by have := hh.2.2.2.1; omega) (by rw [h]; exact hqd.2.2.1.symm) _ hb
    · refine ⟨J (H.sqd), by rw [hb]; exact congrArg (fun n : ℕ => -(n : Om l)) h.symm, key _ _ (hK0 _ hθ _) (hK0 _ ?_ _) (hself _) (hE _) rfl⟩
      exact sqrt_mem_Kur H.q hh.1 (by have := hh.2.2.1; omega) (by rw [h]; exact hqd.2.2.1) _ ha
  refine ⟨main, ?_⟩
  obtain ⟨y, hy, hK⟩ := main
  rw [hK]
  exact sup_le le_sup_left (IntermediateField.adjoin_le_iff.mpr
    (by simpa using sqrt_mem_Ks hl4 Kw y hy))

end Local

theorem preamble_first_clauses (D : D7) (i : D.nd.Loc) (hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    (∃ y : Formalism.BasicNotions.Loc.Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Formalism.BasicNotions.Loc.Om (D.nd.l i)) ∧
      (D.nbr i w hw).Kw.1 = Formalism.BasicNotions.Loc.K0 (D.nbr i w hw).Kw ⊔
        IntermediateField.adjoin ℚ_[D.nd.l i] {y}) ∧
    (D.nbr i w hw).Kw.1 ≤ Formalism.BasicNotions.Loc.Ks (D.nbr i w hw).Kw 1 :=
  local_pre D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) hl (D.nbr i w hw).Kw
    (D.nbr i w hw).j_E (D.nbr i w hw).j_dense

def DegreeClauses (D : D7) : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      Module.finrank ↥(Formalism.BasicNotions.Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 = 2 ∧
      Module.finrank ℚ_[D.nd.l i] ↥(Formalism.BasicNotions.Loc.Ks (D.nbr i w hw).Kw 1) =
        (D.nd.l i - 1) / 2 * Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1

theorem preamble_of_degree_clauses (D : D7) (h : DegreeClauses D) : Conclusion0 D :=
  fun i hl w hw => ⟨(preamble_first_clauses D i hl w hw).1, (preamble_first_clauses D i hl w hw).2, (h i hl w hw).1, (h i hl w hw).2⟩

section Proviso

open Ideal

end Proviso

section Kill

open Formalism.MainNotions.N

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end Kill

end Formalism.MainNotions.EmbeddingTypeJumps

end
end

section
noncomputable section

namespace Formalism.MainNotions.N.PreambleDegrees

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.PreambleDegrees.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finrank_sup_adjoin (F : IntermediateField ℚ_[l] (Om l)) (y : Om l) :
    finrank ℚ_[l] ↥(F ⊔ IntermediateField.adjoin ℚ_[l] {y}) = finrank ℚ_[l] ↥F * (minpoly F y).natDegree := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup, ← IntermediateField.adjoin.finrank hint]
  exact (Module.finrank_mul_finrank ℚ_[l] ↥F ↥(IntermediateField.adjoin F {y})).symm

theorem Ks_eq (K : FinExt l) (s : ℕ) {z : Om l} (hz : IsPrimitiveRoot z (l ^ s)) :
    Ks K s = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {z} := by
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  unfold Ks
  congr 1
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one (show x ^ (l ^ s) = 1 from hx)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  · exact IntermediateField.adjoin.mono _ _ _ (by rintro x rfl; exact hz.pow_eq_one)

theorem finrank_Ks (K : FinExt l) {s : ℕ} (hs : 0 < s) :
    finrank ℚ_[l] ↥(Ks K s) = finrank ℚ_[l] ↥(K0 K) * (l ^ (s - 1) * (l - 1)) := by
  have hz := ζQ_primitive l s
  rw [Ks_eq K s hz, finrank_sup_adjoin, natDegree_minpoly_eq (F := K0 K) inf_le_right hs hz,
    Nat.totient_prime_pow Fact.out hs]

theorem finrank_maxUnramifiedSubfield_padicFinExt_pos (K : FinExt l) : 0 < finrank ℚ_[l] ↥(K0 K) := by
  have := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  exact finrank_pos

theorem sqrt_notMem (y : Om l) (hy : y ^ 2 = -(l : Om l)) : y ∉ MaximalUnramifiedExtension l := by
  intro h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have e : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := (map_natCast _ _).symm
    rw [e]
    exact (PadicAlgCl.norm_extends l _).trans Padic.norm_p
  have h0 : y ≠ 0 := by
    rintro rfl
    have : (l : Om l) = 0 := by simpa using hy.symm
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  obtain ⟨k, hk⟩ := norm_Kur_zpow h h0
  have h2 : ‖y‖ ^ 2 = (l : ℝ)⁻¹ := by rw [← norm_pow, hy, norm_neg, hn]
  have h3 : (l : ℝ) ^ (k * 2) = (l : ℝ) ^ (-1 : ℤ) := by
    rw [zpow_mul, ← hk, zpow_neg_one, ← h2]; norm_cast
  have := zpow_right_injective₀ hl0 hl1.ne' h3
  omega

theorem deg_two (K : FinExt l) (y : Om l) (hy : y ^ 2 = -(l : Om l))
    (hK : K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y}) :
    finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K) * 2 := by
  have hint : IsIntegral (K0 K) y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  have h1 : finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y}) :=
    congrArg (fun F : IntermediateField ℚ_[l] (Om l) => finrank ℚ_[l] ↥F) hK
  rw [h1, finrank_sup_adjoin]
  congr 1
  have hle : (minpoly (K0 K) y).natDegree ≤ 2 := by
    have hm : (Polynomial.X ^ 2 + Polynomial.C (l : ↥(K0 K))).Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
    have hd : (Polynomial.X ^ 2 + Polynomial.C (l : ↥(K0 K))).natDegree = 2 := Polynomial.natDegree_X_pow_add_C
    rw [← hd]
    refine Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ ?_) hm.ne_zero
    simp [hy]
  have hne : (minpoly (K0 K) y).natDegree ≠ 1 := by
    rw [Ne, minpoly.natDegree_eq_one_iff]
    rintro ⟨c, hc⟩
    exact sqrt_notMem y hy (hc ▸ c.2.2)
  have := minpoly.natDegree_pos hint
  omega

theorem preamble_degree_clauses (D : D7) : Formalism.MainNotions.EmbeddingTypeJumps.DegreeClauses D := by
  intro i hl w hw
  obtain ⟨⟨y, hy, hK⟩, -⟩ := Formalism.MainNotions.EmbeddingTypeJumps.preamble_first_clauses D i hl w hw
  have h2 := deg_two _ y hy hK
  have hp := finrank_maxUnramifiedSubfield_padicFinExt_pos (D.nbr i w hw).Kw
  have ht := Module.finrank_mul_finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1
  have hodd : D.nd.l i % 2 = 1 := by
    obtain ⟨-, -, h3, h7, -⟩ := D.host.hyp
    rcases hl with h | h <;> rw [h] <;> omega
  refine ⟨Nat.eq_of_mul_eq_mul_left hp (ht.trans h2), ?_⟩
  rw [finrank_Ks _ one_pos, h2]
  obtain ⟨k, hk⟩ : ∃ k, D.nd.l i - 1 = 2 * k := ⟨(D.nd.l i - 1) / 2, by omega⟩
  rw [hk, Nat.mul_div_cancel_left _ two_pos]
  simp only [Nat.sub_self, pow_zero]
  ring

theorem scaled_lattice_nonzero_holds (D : D7) : Formalism.MainNotions.EmbeddingTypeJumps.Conclusion0 D := Formalism.MainNotions.EmbeddingTypeJumps.preamble_of_degree_clauses D (preamble_degree_clauses D)

theorem vdeg (K : FinExt l) {m : ℕ} (hm : 0 < m) :
    padicValNat l (finrank ℚ_[l] ↥(Ks K m)) - padicValNat l (finrank ℚ_[l] ↥(Ks K 1)) = m - 1 := by
  have hp := finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have h1 : 0 < l - 1 := by have := (Fact.out : l.Prime).one_lt; omega
  have e : finrank ℚ_[l] ↥(Ks K m) = l ^ (m - 1) * finrank ℚ_[l] ↥(Ks K 1) := by
    rw [finrank_Ks K hm, finrank_Ks K one_pos]; simp only [Nat.sub_self, pow_zero]; ring
  have h0 : finrank ℚ_[l] ↥(Ks K 1) ≠ 0 := by
    rw [finrank_Ks K one_pos]
    exact Nat.mul_ne_zero hp.ne' (Nat.mul_ne_zero (pow_pos (Fact.out : l.Prime).pos _).ne' h1.ne')
  rw [e, padicValNat.mul (pow_pos (Fact.out : l.Prime).pos _).ne' h0, padicValNat.prime_pow]
  omega


end Formalism.MainNotions.N.PreambleDegrees
end
end
