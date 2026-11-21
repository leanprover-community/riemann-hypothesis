import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary

section
noncomputable section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GodementSectionReduction

open GlobalTheory.SummCount in

theorem summable_of_count (ι : Type) (n N : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ)
    (h : ι → ℝ) (hb : 1 < b) (ht : (N : ℝ) < t)
    (hh : ∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹)
    (hT : ∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) →
      (T.card : ℝ) ≤ C * ∏ i, b ^ (N * m i)) :
    Summable fun q => h q ^ t := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg N) ht.le
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨q0⟩⟩
  · exact .of_finite
  have hP : ∀ m : Fin n → ℕ, 0 < ∏ i, (b ^ m i)⁻¹ := fun m => by positivity
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (hP (k q0))).1 ((hh q0).1.trans (hh q0).2)
  set r := b ^ ((N : ℝ) - t) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hb0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  set g : (Fin n → ℕ) → ℝ := fun m => C * C ^ t * ∏ i, r ^ m i with hg_def
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg_def]; positivity
  have hg : Summable g :=
    (summable_prod_fin_tuple (summable_geometric_of_lt_one hr0 hr1) (fun _ => pow_nonneg hr0 _)
      n).mul_left _
  have key : ∀ q, h q ^ t ≤ C ^ t * ∏ i, ((b ^ k q i)⁻¹) ^ t := fun q => by
    rw [Real.finset_prod_rpow _ _ (fun i _ => by positivity), ← Real.mul_rpow hC (hP _).le]
    exact Real.rpow_le_rpow (hh q).1 (hh q).2 ht0
  refine summable_of_sum_le (c := ∑' m, g m) (fun q => Real.rpow_nonneg (hh q).1 _) fun T => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := T.image k)
    (fun q hq => Finset.mem_image_of_mem k hq)]
  refine le_trans (Finset.sum_le_sum fun m _ => ?_) (hg.sum_le_tsum _ (fun m _ => hg0 m))
  calc ∑ q ∈ T with k q = m, h q ^ t
      ≤ ∑ q ∈ T with k q = m, C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t :=
        Finset.sum_le_sum fun q hq => by
          have := key q
          rwa [(Finset.mem_filter.1 hq).2] at this
    _ = ((T.filter (k · = m)).card : ℝ) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * ∏ i, b ^ (N * m i)) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) :=
        mul_le_mul_of_nonneg_right (hT m _ fun q hq => (Finset.mem_filter.1 hq).2)
          (mul_nonneg (Real.rpow_nonneg hC _)
            (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _))
    _ = g m := by
        simp only [hg_def, hr, ← pow_mul_inv_rpow_eq hb0 N, Finset.prod_mul_distrib]
        ring

open GlobalTheory.Eis.Conv.CovSkew in

theorem cover_adele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) : ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F ⊗[F] E),
      (Y.card : ℝ) ≤ C * ((4 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ z : AF F ⊗[F] E, ∃ x : E, ∃ y ∈ Y, ∃ ω ∈ Ω,
        z = inclR (F := F) (AF F) x + y + (halfE F E).1 ^ m * ω := by
  classical
  haveI := hσ.1
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact F
  obtain ⟨δ, -, hsp⟩ := exists_delta F E σ hσ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_tens
  have hcont : Continuous fun p : AF F × AF F => psi (F := F) δ p.1 p.2 := by
    unfold psi
    fun_prop
  refine ⟨_, C₀ ^ 2, (hΩ₀.prod hΩ₀).image hcont, fun m => ?_⟩
  obtain ⟨Y, hY, hYc⟩ := hcov m
  refine ⟨(Y ×ˢ Y).image fun y => psi δ y.1 y.2, ?_, fun z => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_self_le_mul_self (Nat.cast_nonneg _) hY).trans (le_of_eq ?_)
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, mul_pow]
    ring
  · obtain ⟨u, v, rfl⟩ := exists_coords δ hsp z
    set c : AF F := algebraMap F (AF F) 2⁻¹ with hc
    have h2 : 2 * c = 1 := by
      rw [hc, ← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    obtain ⟨x, y, hy, ω, hω, e⟩ := hYc (c * (u + v))
    obtain ⟨x', y', hy', ω', hω', e'⟩ := hYc (c * (v - u))
    refine ⟨(x - x') • (1 : E) + (x + x') • δ, _, Finset.mem_image.mpr ⟨(y, y'), Finset.mem_product.2 ⟨hy, hy'⟩, rfl⟩,
      _, ⟨(ω, ω'), ⟨hω, hω'⟩, rfl⟩, ?_⟩
    have : (halfE F E).1 = algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1 := rfl
    rw [this, ← map_pow, ← psi_split, ← e, ← e', psi_eq]
    congr 2
    · linear_combination (-u) * h2
    · linear_combination (-v) * h2

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

abbrev hf (D : D7) : (AE D)ˣ := halfE D.host.F D.host.E

abbrev bs (D : D7) : ℝ := 4 ^ Fintype.card (InfinitePlace D.host.F)

theorem one_lt_bs : 1 < bs D := one_lt_pow₀ (by norm_num) Fintype.card_ne_zero

theorem val_dg (m : Fin r → ℕ) : (dg (hf D) fun i => (m i : ℤ)).1 = diagonal fun i => (hf D).1 ^ m i := by
  simp [dg]

theorem adj_dg (l : Fin r → ℤ) : adj (dg (hf D) l)⁻¹.1 = (dg (hf D) l)⁻¹.1 :=
  congrArg Units.val (cti_dg (σ := cA D) (sigR_halfE D.sp.cm.sig) l)

theorem adj_dg' (l : Fin r → ℤ) : adj (dg (hf D) l).1 = (dg (hf D) l).1 :=
  congrArg Units.inv (cti_dg (σ := cA D) (sigR_halfE D.sp.cm.sig) l)

theorem cover_rect (D : D7) (r n : ℕ) : ∃ (K : Set (Mx D r n)) (C : ℝ), IsCompact K ∧ ∀ m : Fin r → ℕ,
    ∃ Y : Finset (Mx D r n), (Y.card : ℝ) ≤ C * ∏ i, bs D ^ (n * m i) ∧ ∀ x : Mx D r n, ∃ x₀ ∈ ratMx D r n, ∃ y ∈ Y,
      ∃ ω ∈ K, x = x₀ + (y + (dg (hf D) fun i => (m i : ℤ)).1 ⬝ ω) := by
  classical
  obtain ⟨Ω, C, hΩ, h⟩ := cover_adele _ _ _ (AdelicU.isCMExt_host D)
  choose Y hY h using h
  refine ⟨Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω, (C ^ n) ^ r,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ, fun m =>
    ⟨Fintype.piFinset fun i => Fintype.piFinset fun _ => Y (m i), ?_, fun x => ?_⟩⟩
  · have h1 : (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n => Y (m i)).card = ∏ i, (Y (m i)).card ^ n := by
      simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (Nat.cast_le.2 h1.le).trans ?_
    push_cast
    refine (Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY (m i)) n).trans (le_of_eq ?_)
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul _ (m _),
      mul_comm n]
  · choose x₀ y hy ω hω e using fun i j => h (m i) (x i j)
    refine ⟨_, rat_mem (of x₀), of y, Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 (hy i), of ω,
      fun i _ j _ => hω i j, ?_⟩
    ext i j
    rw [val_dg, Matrix.add_apply, Matrix.add_apply, diagonal_mul, ← add_assoc]
    exact e i j

def sk (x : Mx D r r) : skewA D r :=
  ⟨half D • (x - adj x), by rw [mem_skewA, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]⟩

theorem continuous_sk : Continuous (sk : Mx D r r → _) := by
  have := (lattice_Mx D r r).1
  have : ContinuousSub (Mx D r r) := IsTopologicalAddGroup.to_continuousSub
  exact ((continuous_id.sub continuous_adj).const_smul (half D)).subtype_mk _

theorem sk_add (x y : Mx D r r) : sk (x + y) = sk x + sk y := Subtype.ext (by
  change half D • (x + y - adj (x + y)) = half D • (x - adj x) + half D • (y - adj y)
  rw [adj_add, ← smul_add, add_sub_add_comm])

theorem sk_coe (x : skewA D r) : sk x.1 = x := Subtype.ext (by
  change half D • (x.1 - adj x.1) = x.1
  rw [mem_skewA.1 x.2, sub_neg_eq_add, smul_add, half_smul_add])

theorem sk_conj (a x : Mx D r r) : sk (a ⬝ x ⬝ adj a) = skewConj a (sk x) := Subtype.ext (by
  change half D • (a ⬝ x ⬝ adj a - adj (a ⬝ x ⬝ adj a)) = a ⬝ (half D • (x - adj x)) ⬝ adj a
  rw [adj_mul, adj_mul, adj_adj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc a (adj x)])

theorem cover_skewA (D : D7) (r : ℕ) : ∃ (K : Set (skewA D r)) (C : ℝ), IsCompact K ∧ ∀ m : Fin r → ℕ,
    ∃ Y : Finset (skewA D r), (Y.card : ℝ) ≤ C * ∏ i, bs D ^ (r * m i) ∧ ∀ x : skewA D r, ∃ x₀ : skewA D r,
      x₀.1 ∈ ratMx D r r ∧ ∃ y ∈ Y, ∃ ω ∈ K, x = x₀ + (y + skewConj (dg (hf D) fun i => (m i : ℤ)).1 ω) := by
  classical
  have hc := AdelicU.isCMExt_host D
  haveI := hc.1
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact D.host.F
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover _ _ _ hc _ _ _ hΩ₀ hcov r
  have hK : IsCompact (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω : Set (Mx D r r)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ
  refine ⟨_, C, hK.image continuous_sk, fun m => ?_⟩
  obtain ⟨Y, hY, h⟩ := h m
  refine ⟨Finset.image (α := Mx D r r) sk Y, (Nat.cast_le.mpr Finset.card_image_le).trans (hY.trans (le_of_eq ?_)),
    fun x => ?_⟩
  · simp only [bs, ← pow_mul, mul_comm _ 2, show (4 : ℝ) = 2 ^ 2 by norm_num]
  · obtain ⟨S, y, hy, ω, hω, e⟩ := h x.1 x.2
    refine ⟨sk (rat S), ratMx_smul _ (sub_mem (rat_mem _) (ratMx_adj (rat_mem _))), _, Finset.mem_image_of_mem _ hy, _,
      ⟨ω, fun i _ j _ => hω i j, rfl⟩, ?_⟩
    rw [← val_dg] at e
    replace e : x.1 = rat S + y + (dg (hf D) fun i => (m i : ℤ)).1 ⬝ ω ⬝ (dg (hf D) fun i => (m i : ℤ)).1 := e
    rw [← sk_conj, adj_dg', ← sk_add, ← sk_add, ← add_assoc, ← e, sk_coe]

end GlobalTheory.GodementSectionReduction

end
end

section
noncomputable section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GodementSectionReduction

open Formalism.UG (bc)

theorem grp_cover {G : Type} [Group G] {c₀ b₀ B C L e c₁ c₂ y a y' c w w' : G} (h1 : b₀ * B = e * c₁)
    (h2 : c₀ * e = e * c₀) (h3 : c₀ * (c₁ * C) = c₂ * (y' * c)) (h4 : y * a = e * c₂) (h5 : y' * a = a * y')
    (h6 : L * w = a * L) (h7 : L * w' = c * L) : c₀ * b₀ * (B * C * L) = y * y' * L * (w * w') :=
  calc _ = c₀ * (b₀ * B) * C * L := by simp only [mul_assoc]
    _ = e * (c₀ * (c₁ * C)) * L := by rw [h1, ← mul_assoc, h2]; simp only [mul_assoc]
    _ = y * (a * y') * (c * L) := by rw [h3, ← mul_assoc, ← h4]; simp only [mul_assoc]
    _ = y * y' * (a * L) * w' := by rw [← h5, ← h7]; simp only [mul_assoc]
    _ = _ := by rw [← h6]; simp only [mul_assoc]

theorem grp_reduce {G : Type} [Group G] {p u g B B' B'' C C' g' L κ a c : G} (e : p = B * C * g' * L)
    (h1 : g * B = B' * g) (h2 : u * B' = B'' * u) (h3 : g * C = C * g) (h4 : u * C = C' * u) (h5 : g * g' = κ)
    (h6 : κ * L = L * κ) (h7 : u * L = a * c) : u * g * p = B'' * C' * a * (c * κ) :=
  calc _ = u * (g * B) * C * g' * L := by rw [e]; simp only [mul_assoc]
    _ = (u * B') * (g * C) * g' * L := by rw [h1]; simp only [mul_assoc]
    _ = B'' * (u * C) * ((g * g') * L) := by rw [h2, h3]; simp only [mul_assoc]
    _ = B'' * C' * (u * L) * κ := by rw [h4, h5, h6]; simp only [mul_assoc]
    _ = _ := by rw [h7]; simp only [mul_assoc]

theorem add_rearr {A : Type} [AddCommGroup A] {z z' c z'' : A} (e : z - z' = c + z'') : -c + z = z' + z'' := by
  rw [sub_eq_iff_eq_add.1 e]; abel

theorem row_ne_zero {A : Type} [CommRing A] [Nontrivial A] {r n : ℕ} {M : Matrix (Fin r) (Fin n) A}
    {N : Matrix (Fin n) (Fin r) A} (h : M * N = 1) (i : Fin r) : ¬∀ x, M i x = 0 := fun h2 => by
  have h5 := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_zero fun x _ => by rw [h2, zero_mul]] at h5
  exact zero_ne_one h5

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

variable (d : HypDec T T₀ r)

theorem nB_mem (b : Mx D r T₀.rank) : d.nB b ∈ stab d := ⟨1, by rw [d.nB_jX, Units.val_one, Matrix.mul_one]⟩

theorem nC_mem (c : skewA D r) : d.nC c ∈ stab d := ⟨1, by rw [d.nC_jX, Units.val_one, Matrix.mul_one]⟩

theorem wittCoreEmbedding_mem_isotropicStabilizer (g : GA D T₀) : d.emb0 g ∈ stab d := ⟨1, by rw [d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩

theorem cover_rad : ∃ (W : Set (GA D T)) (C : ℝ), IsCompact W ∧ ∀ m : Fin r → ℕ, ∃ Y : Finset (GA D T),
    (Y.card : ℝ) ≤ C * ∏ i, bs D ^ ((T₀.rank + r) * m i) ∧ ∀ b c, ∃ γ ∈ stab d ⊓ GQ T, ∃ y ∈ Y, ∃ w ∈ W,
      γ * (d.nB b * d.nC c * d.levi (dg (hf D) fun i => (m i : ℤ))) = y * d.levi (dg (hf D) fun i => (m i : ℤ)) * w := by
  classical
  obtain ⟨K, C, hK, h⟩ := cover_rect D r T₀.rank
  obtain ⟨K', C', hK', h'⟩ := cover_skewA D r
  refine ⟨_, C * C', (hK.prod hK').image ((d.continuous_nB.comp continuous_fst).mul (d.continuous_nC.comp continuous_snd)),
    fun m => ?_⟩
  obtain ⟨Y, hY, h⟩ := h m
  obtain ⟨Y', hY', h'⟩ := h' m
  refine ⟨(Y ×ˢ Y').image fun y => d.nB y.1 * d.nC y.2, ?_, fun b c => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_le_mul hY hY' (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hY)).trans (le_of_eq ?_)
    simp only [add_mul, pow_add, Finset.prod_mul_distrib]
    ring
  · generalize (dg (hf D) fun i => (m i : ℤ)) = a at *
    obtain ⟨b₀, hb₀, y, hy, ω, hω, e⟩ := h b
    obtain ⟨c₀, hc₀, y', hy', ω', hω', e'⟩ := h' (cComm T₀ (-b₀) b + c - cComm T₀ y (a.1 ⬝ ω))
    refine ⟨d.nC (-c₀) * d.nB (-b₀), mul_mem ⟨nC_mem d _, d.nC_mem_GQ (neg_mem hc₀)⟩ ⟨nB_mem d _, d.nB_mem_GQ (neg_mem hb₀)⟩,
      _, Finset.mem_image.mpr ⟨(y, y'), Finset.mem_product.2 ⟨hy, hy'⟩, rfl⟩, _, ⟨(ω, ω'), ⟨hω, hω'⟩, rfl⟩, ?_⟩
    have h1 := d.nB_mul_nB (-b₀) b
    rw [show -b₀ + b = y + a.1 ⬝ ω from neg_add_eq_iff_eq_add.2 e] at h1
    have h2 : -c₀ + (cComm T₀ (-b₀) b + c) = cComm T₀ y (a.1 ⬝ ω) + (y' + skewConj a.1 ω') := add_rearr e'
    have h3 := congrArg d.nC h2
    rw [d.nC_add, d.nC_add, d.nC_add, d.nC_add] at h3
    exact grp_cover h1 (d.nC_mul_nB _ _) h3 (d.nB_mul_nB _ _) (d.nC_mul_nB _ _) (d.levi_mul_nB _ _) (d.levi_mul_nC _ _)

theorem exists_decomp (p : stab d) : ∃ b c g, (p : GA D T) = d.nB b * d.nC c * d.emb0 g * d.levi (onX d p) := by
  have h : (p : GA D T) * d.levi (onX d p)⁻¹ ∈ MixPer.stabX d := by
    show mt T (p * d.levi (onX d p)⁻¹) ⬝ d.jX = d.jX
    rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.levi_jX, cancel₂ (mul_jX d p), Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  obtain ⟨n, hn, g, e⟩ := (MixPer.Decomp.mem_stabX_iff d).1 h
  obtain ⟨b, c, rfl⟩ := (MixPer.Decomp.mem_radX_iff d).1 hn
  exact ⟨b, c, g, by rw [← e, map_inv, inv_mul_cancel_right]⟩

theorem reduction_GL_diagonalUnitPowers_compact {E A : Type} [Field E] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (j : E →+* A) {s : Aˣ} {ν : Aˣ →* ℝ≥0} (hν : Continuous ν) (hj : ∀ u : Eˣ, ν (Units.map j.toMonoidHom u) = 1)
    {b : ℝ} (hb : 0 < b) (hs : (ν s : ℝ) = b⁻¹) {r : ℕ}
    (hR : ∃ Ω : Set A, IsCompact Ω ∧ ∀ β : GL (Fin r) A, ∃ (δ : GL (Fin r) E) (l : Fin r → ℤ) (c : GL (Fin r) A),
      (∀ i k, c.1 i k ∈ Ω ∧ c⁻¹.1 i k ∈ Ω) ∧ δ.1.map j * β.1 = diagonal (fun i => (s ^ l i).1) * c.1) :
    ∃ (L : Set (GL (Fin r) A)) (C : ℝ), IsCompact L ∧ ∀ α : GL (Fin r) A,
    ∃ (δ : GL (Fin r) E) (l : Fin r → ℤ), ∃ c ∈ L, bc j δ * α = dg s l * c ∧
      (ν (GeneralLinearGroup.det α) : ℝ) ≤ C * ∏ i, (b ^ l i)⁻¹ := by
  obtain ⟨Ω, hΩ, hR⟩ := hR
  choose δ l c hcΩ hred using hR
  replace hred : ∀ β, bc j (δ β) * β = dg s (l β) * c β := fun β => Units.ext (hred β)
  obtain ⟨L, hL, hcL⟩ : Bdd c :=
    bdd_units (bdd_matrix hΩ fun q i k => (hcΩ q i k).1) (bdd_matrix hΩ fun q i k => (hcΩ q i k).2)
  have hdet : Continuous (GeneralLinearGroup.det : GL (Fin r) A → Aˣ) := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  obtain ⟨B, hB⟩ := (hL.image (NNReal.continuous_coe.comp (hν.comp hdet))).bddAbove
  refine ⟨L, B, hL, fun α => ⟨δ α, l α, c α, hcL α, hred α, ?_⟩⟩
  have h1 : GeneralLinearGroup.det (bc j (δ α)) = Units.map j.toMonoidHom (GeneralLinearGroup.det (δ α)) :=
    Units.ext (j.map_det (δ α).1).symm
  have h3 := congrArg (fun x => (ν (GeneralLinearGroup.det x) : ℝ)) (hred α)
  beta_reduce at h3
  rw [map_mul, map_mul, map_mul, map_mul, h1, hj, one_mul, det_dg, map_prod, NNReal.coe_mul, NNReal.coe_prod] at h3
  have h4 : ∀ i, (ν (s ^ l α i) : ℝ) = (b ^ l α i)⁻¹ := fun i => by
    rw [map_zpow, NNReal.coe_zpow, hs, _root_.inv_zpow]
  rw [h3, mul_comm, Finset.prod_congr rfl fun i _ => h4 i]
  exact mul_le_mul_of_nonneg_right (hB ⟨_, hcL α, rfl⟩) (by positivity)

theorem reduce_gl (D : D7) (r : ℕ) : ∃ (L : Set (GL (Fin r) (AE D))) (C : ℝ), IsCompact L ∧ ∀ α : GL (Fin r) (AE D),
    ∃ (δ : GL (Fin r) D.host.E) (l : Fin r → ℤ), ∃ c ∈ L, bc (incA D) δ * α = dg (hf D) l * c ∧
      (absA D (GeneralLinearGroup.det α) : ℝ) ≤ C * ∏ i, (bs D ^ l i)⁻¹ :=
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc := AdelicU.isCMExt_host D
  reduction_GL_diagonalUnitPowers_compact (incA D) continuous_absE (fun u => absE_inclR u) (one_pos.trans one_lt_bs)
    (by rw [GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity _ _ _ hc]; simp) (red_gl _ _ _ hc r)

theorem reduce (h₀ : IsAniso T₀) : ∃ (W : Set (GA D T)) (C : ℝ), IsCompact W ∧ ∀ p : stab d, ∃ γ ∈ stab d ⊓ GQ T,
    ∃ b c, ∃ l : Fin r → ℤ, ∃ w ∈ W, γ * p = d.nB b * d.nC c * d.levi (dg (hf D) l) * w ∧
      (absDet d p : ℝ) ≤ C * ∏ i, (bs D ^ l i)⁻¹ := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D T₀ h₀
  obtain ⟨L, B, hL, hR⟩ := reduce_gl D r
  have hcont : Continuous fun x : GL (Fin r) (AE D) × GA D T₀ => d.levi x.1 * d.emb0 x.2 :=
    (d.continuous_levi.comp continuous_fst).mul (d.continuous_embed.comp continuous_snd)
  refine ⟨_, B, (hL.prod hK).image hcont, fun p => ?_⟩
  obtain ⟨b, s, g, e⟩ := exists_decomp d p
  obtain ⟨g₀, hg₀, κ, hκ, rfl⟩ := hcov g
  obtain ⟨δ, l, c, hc, hred, hle⟩ := hR (onX d p)
  have h1 : d.levi (bc (incA D) δ) ∈ GQ T := d.levi_mem_GQ (rat_mem δ.1) (rat_mem (δ⁻¹).1)
  generalize bc (incA D) δ = u at h1 hred
  exact ⟨d.levi u * d.emb0 g₀⁻¹, mul_mem ⟨levi_mem d _, h1⟩ ⟨wittCoreEmbedding_mem_isotropicStabilizer d _, d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (inv_mem hg₀)⟩,
    u.1 ⬝ (b ⬝ mt T₀ g₀⁻¹⁻¹), skewConj u.1 s, l, d.levi c * d.emb0 κ, ⟨(c, κ), ⟨hc, hκ⟩, rfl⟩,
    grp_reduce e (d.wittHyperbolic_anisotropic_conj_nB _ _) (d.levi_mul_nB _ _) (d.wittHyperbolic_anisotropic_commute_nC _ _) (d.levi_mul_nC _ _)
      ((map_mul d.emb0 _ _).symm.trans (congrArg d.emb0 (inv_mul_cancel_left g₀ κ))) (d.wittHyperbolic_anisotropic_commute_levi _ _)
      ((map_mul d.levi _ _).symm.trans ((congrArg d.levi hred).trans (map_mul d.levi _ _))), hle⟩

theorem pY_mul (b : Mx D r T₀.rank) (c : skewA D r) (a : GL (Fin r) (AE D)) (w : GA D T) :
    d.pY ⬝ mt T (d.nB b * d.nC c * d.levi a * w) = adj a⁻¹.1 ⬝ (d.pY ⬝ mt T w) := by
  rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, d.pY_nB, d.pY_nC, d.pY_levi, Matrix.mul_assoc]

theorem pY_row (g : GA D T) (i : Fin r) : ¬∀ x, (d.pY ⬝ mt T g) i x = 0 :=
  haveI : Nontrivial (AE D) := incA_injective.nontrivial
  have h4 : mt T g ⬝ (mt T g⁻¹ ⬝ d.jY) = d.jY := (cancel₂ (mt_mul_inv T g) d.jY).trans (Matrix.one_mul _)
  row_ne_zero ((Matrix.mul_assoc _ _ _).trans ((congrArg (d.pY ⬝ ·) h4).trans d.pY_jY)) i

theorem bound_aux {E A : Type} [Field E] [CommRing A] (j : E →+* A) {s : Aˣ} {Ω : Set A} {m₀ r n : ℕ}
    (hm₀ : ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, j x = s.1 ^ m * ω → x = 0) {l : Fin r → ℤ} {y : Matrix (Fin r) (Fin n) E}
    {w : Matrix (Fin r) (Fin n) A} (hw : ∀ i x, w i x ∈ Ω) (e : y.map j = (dg s l)⁻¹.1 * w) (i : Fin r)
    (h : ¬∀ x, y.map j i x = 0) : -(m₀ : ℤ) ≤ l i := by
  by_contra! hlt
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := -l i) (by omega)
  refine h fun x => ?_
  have h3 : j (y i x) = s.1 ^ m * w i x := by
    refine (congrFun (congrFun e i) x).trans ?_
    rw [show (dg s l)⁻¹.1 = diagonal fun i => (s ^ l i)⁻¹.1 from rfl, diagonal_mul, ← _root_.zpow_neg, hm, zpow_natCast,
      Units.val_pow_eq_pow_val]
  rw [map_apply, hm₀ m (by omega) _ (hw i x) _ h3, map_zero]

theorem exists_bound {W : Set (GA D T)} (hW : IsCompact W) : ∃ m₀ : ℕ, ∀ b c (l : Fin r → ℤ), ∀ w ∈ W,
    d.nB b * d.nC c * d.levi (dg (hf D) l) * w ∈ GQ T → ∀ i, -(m₀ : ℤ) ≤ l i := by
  have hc : Continuous fun w : GA D T => d.pY ⬝ mt T w := continuous_const.matrix_mul (continuous_mt T)
  have hb : Bdd fun w : W => (w : GA D T) := ⟨W, hW, fun w => w.2⟩
  obtain ⟨Ω, hΩ, h⟩ := (hb.map hc).entries
  obtain ⟨m₀, hm₀⟩ := (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero _ _ Ω hΩ).2
  refine ⟨m₀, fun b c l w hw hg i => ?_⟩
  have h1 := pY_mul d b c (dg (hf D) l) w
  have h2 := pY_row d (d.nB b * d.nC c * d.levi (dg (hf D) l) * w) i
  rw [adj_dg] at h1
  generalize d.nB b * d.nC c * d.levi (dg (hf D) l) * w = g at hg h1 h2
  obtain ⟨y, hy⟩ := mem_ratMx.1 (ratMx_mul (rat_mem d.qY) ((mem_GQ_iff T g).1 hg))
  replace hy : rat y = d.pY ⬝ mt T g := hy
  rw [← hy] at h1 h2
  exact bound_aux (incA D) hm₀ (h ⟨w, hw⟩) h1 i h2

theorem dg_sub (s : (AE D)ˣ) (m : Fin r → ℕ) (m₀ : ℤ) :
    (dg s fun i => (m i : ℤ) + m₀) = (dg s fun i => (m i : ℤ)) * dg s fun _ => m₀ := Units.ext (by
  change diagonal _ = diagonal _ * diagonal _
  rw [diagonal_mul_diagonal]
  exact congrArg diagonal (funext fun i => congrArg Units.val (_root_.zpow_add s _ _)))

theorem grp_count {G : Type} [Group G] {γ' γ x p k n a z w y w' : G} (e : x = p * k) (h1 : γ * p = n * (a * z) * w)
    (h2 : γ' * (n * a) = y * a * w') : γ' * γ * x = y * a * (w' * z * w * k) :=
  calc _ = γ' * (γ * p) * k := by rw [e]; simp only [mul_assoc]
    _ = γ' * (n * a) * (z * w * k) := by rw [h1]; simp only [mul_assoc]
    _ = _ := by rw [h2]; simp only [mul_assoc]

theorem exists_card_le' {Q : Type} {Z w : Q → GA D T} (hZ : ∀ q, Z q ∈ GQ T) (hi : Function.Injective Z) (hw : Bdd w) :
    ∃ N : ℕ, ∀ (z : GA D T) (S : Finset Q), (∀ q ∈ S, Z q = z * w q) → S.card ≤ N := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : Nontrivial (AE D) := incA_injective.nontrivial
  have he := AdelicU.isEmbedding_matHom (AF D.host.F) D.sp.cm.sig T.gram
  obtain ⟨N, hN⟩ := exists_card_le (incA D) (fun Ω h => (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero _ _ Ω h).1)
    (Z := fun q => AdelicU.matHom _ D.sp.cm.sig T.gram (Z q)) (fun q => (mem_rat _).2 fun a b => by
      obtain ⟨y, hy⟩ := mem_ratMx.1 ((mem_GQ_iff T _).1 (hZ q))
      exact ⟨y a b, congrFun (congrFun hy a) b⟩) (he.injective.comp hi) (hw.map he.continuous)
  exact ⟨N, fun z S h => hN (AdelicU.matHom _ D.sp.cm.sig T.gram z) S fun q hq =>
    (congrArg _ (h q hq)).trans (map_mul _ _ _)⟩

theorem summable_absDet (h₀ : IsAniso T₀) {Q : Type} {x k : Q → GA D T} {p : Q → stab d} (hx : ∀ q, x q ∈ GQ T)
    (e : ∀ q, x q = p q * k q) (hk : Bdd k) (hi : ∀ q q', ∀ γ ∈ stab d, x q' = γ * x q → q = q') {t : ℝ}
    (ht : ((T₀.rank + r : ℕ) : ℝ) < t) : Summable fun q => (absDet d (p q) : ℝ) ^ t := by
  classical
  have hb := one_lt_bs (D := D)
  have hb0 := one_pos.trans hb
  obtain ⟨W, B, hW, hR⟩ := reduce d h₀
  choose γ hγ b c l w hw hred hle using fun q => hR (p q)
  have hwb : Bdd w := ⟨W, hW, hw⟩
  obtain ⟨W₁, hW₁, hw₁⟩ := hwb.mul hk
  obtain ⟨m₀, hm₀⟩ := exists_bound d hW₁
  have hl : ∀ q i, -(m₀ : ℤ) ≤ l q i := fun q => hm₀ (b q) (c q) (l q) _ (hw₁ q) (by
    have := mul_mem (hγ q).2 (hx q)
    rwa [e, ← mul_assoc, hred, mul_assoc _ (w q)] at this)
  obtain ⟨m, hm⟩ : ∃ m : Q → Fin r → ℕ, ∀ q, l q = fun i => (m q i : ℤ) + -(m₀ : ℤ) :=
    ⟨fun q i => (l q i + m₀).toNat, fun q => funext fun i => by have := hl q i; beta_reduce; omega⟩
  obtain ⟨W₂, C, hW₂, hC⟩ := cover_rad d
  choose Y hY hC using hC
  choose γ' hγ' y hy w' hw' hcov using fun q => hC (m q) (b q) (c q)
  have hw'b : Bdd w' := ⟨W₂, hW₂, hw'⟩
  have h4 : ∀ q, γ' q * γ q * x q = y q * d.levi (dg (hf D) fun i => (m q i : ℤ)) *
      (w' q * d.levi (dg (hf D) fun _ => -(m₀ : ℤ)) * w q * k q) := fun q =>
    grp_count (e q) (by rw [hred, hm, dg_sub, map_mul]) (hcov q)
  obtain ⟨N, hN⟩ := exists_card_le' (Z := fun q => γ' q * γ q * x q)
    (fun q => mul_mem (mul_mem (hγ' q).2 (hγ q).2) (hx q))
    (fun q q' h => hi q q' ((γ' q' * γ q')⁻¹ * (γ' q * γ q))
      (mul_mem (inv_mem (mul_mem (hγ' q').1 (hγ q').1)) (mul_mem (hγ' q).1 (hγ q).1))
      ((eq_inv_mul_iff_mul_eq.2 h.symm).trans (mul_assoc _ _ _).symm))
    (((hw'b.mul (Bdd.const (d.levi (dg (hf D) fun _ => -(m₀ : ℤ))))).mul hwb).mul hk)
  refine summable_of_count Q r (T₀.rank + r) (bs D) (max (B * bs D ^ (m₀ * r)) (N * C)) t m _ hb ht
    (fun q => ⟨NNReal.coe_nonneg _, ?_⟩) fun μ S hS => ?_
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    refine (hle q).trans (le_of_eq ?_)
    rw [mul_assoc, hm]
    simp only [zpow_add₀ hb0.ne', _root_.zpow_neg, zpow_natCast, mul_inv, inv_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [mul_comm (∏ _, _)]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have h10 : S.card ≤ N * (Y μ).card := Finset.card_le_mul_card_image_of_maps_to
      (fun q hq => hS q hq ▸ hy q) N fun z _ => hN (z * d.levi (dg (hf D) fun i => (μ i : ℤ))) _
        fun q hq => by rw [h4, (Finset.mem_filter.1 hq).2, hS q (Finset.mem_filter.1 hq).1]
    rw [mul_assoc]
    exact (Nat.cast_le.2 h10).trans (by push_cast; exact mul_le_mul_of_nonneg_left (hY μ) (Nat.cast_nonneg _))

end GlobalTheory.GodementSectionReduction

end
end
