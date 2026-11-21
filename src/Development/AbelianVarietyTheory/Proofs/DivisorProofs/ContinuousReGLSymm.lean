import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinClAndGamOrd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenComapProdLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.SymImageC

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def refLev (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p + 1) (fun i => 2 * (i.val + 1))

def refGroup (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | GlobalTheory.RootEx.Radical.Uni (refLev p) g.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun ha hb => GlobalTheory.RootEx.Radical.Uni.mul ha hb
  inv_mem' := fun ha => GlobalTheory.RootEx.Radical.Uni.inv ha

theorem N_le_refGroup {p q : ℕ} (h₁ : p ≤ q) (h₂ : q ≤ p + 1) :
    GlobalTheory.RootEx.N k n c q ≤ refGroup k n c p := by
  intro g hg r s hrs
  refine (GlobalTheory.RootEx.Radical.mem_N_iff g).1 hg r s ?_
  rcases r with r | r <;> rcases s with s | s <;>
    simp only [refLev, Sum.elim_inl, Sum.elim_inr] at hrs <;>
    simp only [GlobalTheory.RootEx.lev, Sum.elim_inl, Sum.elim_inr] <;> omega

theorem symN_le_refGroup : symN k n c ≤ refGroup k n c ((c + 1) / 2) :=
  sup_le (N_le_refGroup le_rfl (by omega)) (N_le_refGroup (by omega) (by omega))

theorem toBlocks₁₁_of_mem_symN {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) : u.val.toBlocks₁₁ = 1 := by
  have h : GlobalTheory.RootEx.Radical.Uni (refLev ((c + 1) / 2)) u.val := symN_le_refGroup hu
  ext r s
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
  rw [h _ _ (by simp [refLev])]
  simp [Matrix.one_apply]

theorem toBlocks₁₁_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    (u * GlobalTheory.RootEx.embX c g).val.toBlocks₁₁ = g.val := by
  have h := toBlocks₁₁_of_mem_symN hu
  rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks u.val]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, h]
  simp

theorem toBlocks₁₁_inv_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    ((u * GlobalTheory.RootEx.embX c g)⁻¹).val.toBlocks₁₁ = (g⁻¹).val := by
  have h := toBlocks₁₁_of_mem_symN (inv_mem hu)
  rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, GlobalTheory.RootEx.Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (u⁻¹).val]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, h]
  simp

end GlobalTheory.FunObj.SymImageC

open GlobalTheory.FunObj.SymImageC in

theorem GlobalTheory.FunObj.SymImageC.symPr_open_bounded {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (C : Subgroup (GL (n ⊕ Fin c) k)) (hC : IsOpen (C : Set (GL (n ⊕ Fin c) k)))
    (hb : ∃ A : Set (GL (n ⊕ Fin c) k), IsCompact A ∧ (C : Set (GL (n ⊕ Fin c) k)) ⊆ A) :
    IsOpen (symPr C : Set (GL n k)) ∧ ∃ A : Set (GL n k), IsCompact A ∧ (symPr C : Set (GL n k)) ⊆ A := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  constructor
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    have ho := hC.preimage (GlobalTheory.RootEx.QuotLinear.continuous_embX (k := k) (n := n) (c := c))
    refine Filter.mem_of_superset (ho.mem_nhds (by simp [one_mem])) fun g hg => ?_
    exact ⟨1, one_mem _, by simpa using hg⟩
  · obtain ⟨A, hA, hCA⟩ := hb
    let φ : GL (n ⊕ Fin c) k → Matrix n n k × (Matrix n n k)ᵐᵒᵖ :=
      fun g => (g.val.toBlocks₁₁, MulOpposite.op (g⁻¹).val.toBlocks₁₁)
    have hbl : Continuous fun M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => M.toBlocks₁₁ :=
      continuous_matrix fun i j => continuous_id.matrix_elem _ _
    have hφ : Continuous φ :=
      (hbl.comp Units.continuous_val).prodMk
        (MulOpposite.continuous_op.comp (hbl.comp Units.continuous_coe_inv))
    refine ⟨_, (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hA.image hφ),
      ?_⟩
    rintro g ⟨u, hu, h⟩
    refine ⟨_, hCA h, ?_⟩
    simp only [φ]
    rw [toBlocks₁₁_mul_embX hu, toBlocks₁₁_inv_mul_embX hu]
    rfl
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

open GlobalTheory.StdFrames (cpt sg OA mem_OA_iff)
open GlobalTheory.IdemSupport (cP)

namespace GlobalTheory.ProdLevCompactC

variable {D : D7}

def BdAt (Q : Pl D.host.E) (N : ℕ) {a b : ℕ} (M : Matrix (Fin a) (Fin b) (Lev.EAf D)) : Prop :=
  ∀ i j, Valued.v (cpt Q ((N : Lev.EAf D) * M i j)) ≤ 1

theorem v_natCast_le (Q : Pl D.host.E) (N : ℕ) : Valued.v (cpt Q (N : Lev.EAf D)) ≤ 1 := by
  rw [map_natCast]
  exact natCast_mem (Q.adicCompletionIntegers D.host.E).toSubring N

theorem BdAt.mono {Q : Pl D.host.E} {N : ℕ} {a b : ℕ} {M : Matrix (Fin a) (Fin b) (Lev.EAf D)} (h : BdAt Q N M)
    (N' : ℕ) : BdAt Q (N' * N) M := fun i j => by
  rw [Nat.cast_mul, mul_assoc, map_mul, Valuation.map_mul]
  exact mul_le_one' (v_natCast_le Q N') (h i j)

theorem BdAt.mul {Q : Pl D.host.E} {N N' : ℕ} {a b c : ℕ} {A : Matrix (Fin a) (Fin b) (Lev.EAf D)}
    {B : Matrix (Fin b) (Fin c) (Lev.EAf D)} (hA : BdAt Q N A) (hB : BdAt Q N' B) : BdAt Q (N * N') (A * B) := by
  intro i j
  have : ((N * N' : ℕ) : Lev.EAf D) * (A * B) i j = ∑ k, ((N : Lev.EAf D) * A i k) * ((N' : Lev.EAf D) * B k j) := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [this, map_sum]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul, Valuation.map_mul]
  exact mul_le_one' (hA i k) (hB k j)

theorem BdAt.of_int {Q : Pl D.host.E} {a b : ℕ} {M : Matrix (Fin a) (Fin b) (Lev.EAf D)}
    (h : ∀ i j, Valued.v (cpt Q (M i j)) ≤ 1) (N : ℕ) : BdAt Q N M := fun i j => by
  rw [map_mul, Valuation.map_mul]
  exact mul_le_one' (v_natCast_le Q N) (h i j)

theorem inBasis_apply {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (x : GL (Fin n) (Lev.EAf D))
    (i j : Fin n) : (GlobalTheory.FunObj.inBasis h β w x).val (finCongr h.symm i) (finCongr h.symm j) = cpt w ((β⁻¹ * x * β).val i j) := by
  simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

theorem BdAt.dvd {Q : Pl D.host.E} {N N' : ℕ} {a b : ℕ} {M : Matrix (Fin a) (Fin b) (Lev.EAf D)} (h : BdAt Q N M)
    (hd : N ∣ N') : BdAt Q N' M := by
  obtain ⟨c, rfl⟩ := hd
  rw [mul_comm]
  exact h.mono c

theorem exists_nat_mul_le_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (C : Set (w.adicCompletion E)) (hC : IsCompact C) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ c ∈ C, Valued.v ((N : w.adicCompletion E) * c) ≤ 1 := by
  set p : ℕ := Ideal.absNorm w.asIdeal with hp
  have hp0 : p ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  have hv : Valued.v (p : w.adicCompletion E) < 1 := by
    have := (w.valuation_lt_one_iff_mem (K := E) (p : 𝓞 E)).2 (Ideal.absNorm_mem w.asIdeal)
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  let U : ℕ → Set (w.adicCompletion E) := fun m => {c | Valued.v ((p : w.adicCompletion E) ^ m * c) ≤ 1}
  have hU : ∀ m, IsOpen (U m) := fun m =>
    (GlobalTheory.Mem.UnitOpen.isOpen_val_le w 0).preimage (continuous_const.mul continuous_id)
  have hmono : Monotone U := by
    refine monotone_nat_of_le_succ fun m c hc => ?_
    change Valued.v ((p : w.adicCompletion E) ^ (m + 1) * c) ≤ 1
    rw [pow_succ', mul_assoc, Valuation.map_mul]
    exact mul_le_one' hv.le hc
  have hcov : C ⊆ ⋃ m, U m := by
    intro c _
    refine Set.mem_iUnion.2 ?_
    by_cases h0 : Valued.v c = 0
    · exact ⟨0, by change Valued.v (_ * c) ≤ 1; rw [Valuation.map_mul, h0, mul_zero]; exact zero_le⟩
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hv (Units.mk0 _ h0)⁻¹
    refine ⟨m, ?_⟩
    change Valued.v (_ * c) ≤ 1
    rw [Valuation.map_mul, Valuation.map_pow]
    rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hm
    calc Valued.v (p : w.adicCompletion E) ^ m * Valued.v c ≤ (Valued.v c)⁻¹ * Valued.v c :=
          by gcongr
      _ = 1 := inv_mul_cancel₀ h0
  obtain ⟨m, hm⟩ := hC.elim_directed_cover U hU hcov hmono.directed_le
  refine ⟨p ^ m, pow_ne_zero _ hp0, fun c hc => ?_⟩
  rw [Nat.cast_pow]
  exact hm hc

theorem exists_bdAt (Q : Pl D.host.E) {a b : ℕ} (M : Matrix (Fin a) (Fin b) (Lev.EAf D)) : ∃ N : ℕ, N ≠ 0 ∧ BdAt Q N M := by
  obtain ⟨N, hN, h⟩ := exists_nat_mul_le_one Q (Set.range fun p : Fin a × Fin b => cpt Q (M p.1 p.2))
    (Set.finite_range _).isCompact
  refine ⟨N, hN, fun i j => ?_⟩
  rw [map_mul, map_natCast]
  exact h _ ⟨(i, j), rfl⟩

theorem bdAt_cP (V : HSp D) (w : Pl D.host.E) : ∃ M : ℕ, M ≠ 0 ∧ ∀ (N : ℕ) (x : GL (Fin V.rank) (Lev.EAf D)),
    x ∈ UA D.sp.cm V.gram → BdAt w N (x⁻¹).val → BdAt (cP w) (M * N) x.val := by
  obtain ⟨M₁, h₁, hM₁⟩ := exists_bdAt (cP w) (V.gram⁻¹.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))
  obtain ⟨M₂, h₂, hM₂⟩ := exists_bdAt (cP w) (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))
  refine ⟨M₁ * M₂, mul_ne_zero h₁ h₂, fun N x hx hN => ?_⟩
  set J := V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  set J' := V.gram⁻¹.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  have hJ : J' * J = 1 := by
    simp only [J, J']
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit (GlobalTheory.StabCompact.det_gram_ne_zero V)),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : Formalism.UG.cT (sg D) (x⁻¹).val * J * (x⁻¹).val = J := (UA D.sp.cm V.gram).inv_mem hx
  have e : x.val = J' * Formalism.UG.cT (sg D) (x⁻¹).val * J := by
    have := congrArg (· * x.val) hu
    simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one] at this
    rw [Matrix.mul_assoc, this, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hc : BdAt (cP w) N (Formalism.UG.cT (sg D) (x⁻¹).val) := fun i j => by
    have h1 : (N : Lev.EAf D) * Formalism.UG.cT (sg D) (x⁻¹).val i j = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D ((N : Lev.EAf D) * (x⁻¹).val j i) := by
      change _ = sg D _
      rw [map_mul, map_natCast]
      rfl
    rw [h1, GlobalTheory.AdIsom.cpt_cjA_le_iff]
    exact hN j i
  rw [e]
  have := (hM₁.mul hc).mul hM₂
  refine this.dvd ?_
  exact ⟨1, by ring⟩

theorem bdAt_mem {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (h : ∀ w, n' w = n)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (w : P)
    (hK : ∃ C : Set (GL (Fin (n' w)) (Kw w.1)), IsCompact C ∧ (K w : Set (GL (Fin (n' w)) (Kw w.1))) ⊆ C) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ z ∈ GlobalTheory.FunObj.prodLev β P h K, BdAt w.1 N (β⁻¹ * z * β).val := by
  obtain ⟨C, hC, hKC⟩ := hK
  obtain ⟨N, hN, hb⟩ := exists_nat_mul_le_one w.1
    (⋃ p : Fin (n' w) × Fin (n' w), (fun g : GL (Fin (n' w)) (Kw w.1) => g.val p.1 p.2) '' C)
    (isCompact_iUnion fun p => hC.image (Units.continuous_val.matrix_elem p.1 p.2))
  refine ⟨N, hN, fun z hz i j => ?_⟩
  have h1 : GlobalTheory.FunObj.inBasis (h w) β w.1 z ∈ K w := Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hz).1 w
  rw [map_mul, map_natCast, ← inBasis_apply (h w)]
  exact hb _ (Set.mem_iUnion.2 ⟨(finCongr (h w).symm i, finCongr (h w).symm j), _, hKC h1, rfl⟩)

theorem int_off {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (h : ∀ w, n' w = n)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (Q : Pl D.host.E)
    (hQ : ∀ w ∈ P, Q.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) (z : GL (Fin n) (Lev.EAf D))
    (hz : z ∈ GlobalTheory.FunObj.prodLev β P h K) (i j : Fin n) : Valued.v (cpt Q ((β⁻¹ * z * β).val i j)) ≤ 1 := by
  have h1 : GlobalTheory.FunObj.inBasis rfl β Q z ∈ GlobalTheory.SplitWeil.KO (Kw Q) (Fin n) :=
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hz).2 Q) hQ
  have h2 := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 h1).1 (finCongr rfl i) (finCongr rfl j)
  rw [inBasis_apply rfl] at h2
  rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff] at h2
  have h3 : Valued.v (cpt Q ((β⁻¹ * z * β).val i j)) ≤ Valued.v (1 : Kw Q) := h2
  rwa [map_one] at h3

theorem exists_bd (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ}
    (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1)))
    (hK : ∀ w, ∃ C : Set (GL (Fin (n' w)) (Kw w.1)), IsCompact C ∧ (K w : Set (GL (Fin (n' w)) (Kw w.1))) ⊆ C) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ z ∈ GlobalTheory.FunObj.prodLev β P h K, z ∈ UA D.sp.cm V.gram →
      ∀ Q : Pl D.host.E, BdAt Q N (β⁻¹ * z * β).val := by
  choose N₁ hN₁ hb₁ using fun w : P => bdAt_mem β P h K w (hK w)
  choose Nb hNb hbb using fun w : P => exists_bdAt w.1 β.val
  choose Nb' hNb' hbb' using fun w : P => exists_bdAt w.1 (β⁻¹).val
  choose M hM hbM using fun w : P => bdAt_cP V w.1
  choose Nc hNc hbc using fun w : P => exists_bdAt (cP w.1) (β⁻¹).val
  choose Nc' hNc' hbc' using fun w : P => exists_bdAt (cP w.1) β.val
  let B : P → ℕ := fun w => Nc w * (M w * (Nb w * N₁ w * Nb' w)) * Nc' w
  refine ⟨∏ w : P, N₁ w * B w, Finset.prod_ne_zero_iff.2 fun w _ => mul_ne_zero (hN₁ w)
    (mul_ne_zero (mul_ne_zero (hNc w) (mul_ne_zero (hM w) (mul_ne_zero (mul_ne_zero (hNb w) (hN₁ w)) (hNb' w))))
      (hNc' w)), fun z hz hu Q => ?_⟩
  have hd : ∀ w : P, N₁ w * B w ∣ ∏ w : P, N₁ w * B w := fun w => Finset.dvd_prod_of_mem _ (Finset.mem_univ w)
  have hy : ∀ w : P, BdAt (cP w.1) (B w) (β⁻¹ * z * β).val := fun w => by
    have e1 : (z⁻¹).val = β.val * (β⁻¹ * z⁻¹ * β).val * (β⁻¹).val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    have h1 : BdAt w.1 (Nb w * N₁ w * Nb' w) (z⁻¹).val := by
      rw [e1]
      exact ((hbb w).mul (hb₁ w _ (inv_mem hz))).mul (hbb' w)
    have h2 := hbM w _ z hu h1
    have e2 : (β⁻¹ * z * β).val = (β⁻¹).val * z.val * β.val := by rw [Units.val_mul, Units.val_mul]
    rw [e2]
    exact ((hbc w).mul h2).mul (hbc' w)
  by_cases hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)
  · obtain ⟨w, hw, e⟩ := hQ
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP e with rfl | rfl
    · exact (hb₁ ⟨Q, hw⟩ z hz).dvd ((dvd_mul_right _ _).trans (hd ⟨Q, hw⟩))
    · exact (hy ⟨w, hw⟩).dvd ((dvd_mul_left _ _).trans (hd ⟨w, hw⟩))
  · push Not at hQ
    exact BdAt.of_int (int_off β P h K Q hQ z hz) _

theorem exists_compact_entries_bd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) (N : ℕ) (hN : N ≠ 0) :
    ∃ C : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E), IsCompact C ∧ ∀ x : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E),
      (∀ i j, (N : E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) *
        (β⁻¹ * Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) : _ →+* _) x * β).1 i j ∈
          Formalism.L2.Herm.intAf F E) → ∀ i j, x.1 i j ∈ C := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
  obtain ⟨C, hc, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact F E).2
  set s := GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  let β' : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E := algebraMap F _ (N : F)⁻¹
  have hc1 : c * (N : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) = 1 := by
    rw [← map_natCast (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN), map_one]
  let C₁ : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := (fun t => c * t) '' C
  have hC₁ : IsCompact C₁ := hc.image (continuous_const.mul continuous_id)
  let S : Set (Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C₁
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC₁
  refine ⟨⋃ p : Fin n × Fin n, (fun A : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) =>
      (β'.1 * A * (β'⁻¹).1) p.1 p.2) '' S,
    isCompact_iUnion fun p => hS.image
      (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem _ _), ?_⟩
  intro x hx i j
  refine Set.mem_iUnion.2 ⟨(i, j), (β'⁻¹ * x * β').1, fun a _ b _ => ?_, ?_⟩
  · have hs : Formalism.UG.bc (s : _ →+* _) (β'⁻¹ * x * β') = β⁻¹ * Formalism.UG.bc (s : _ →+* _) x * β := by
      rw [map_mul, map_mul, map_inv, hβ]
    refine ⟨(N : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) * (β'⁻¹ * x * β').1 a b, hCe _ ?_, ?_⟩
    · show s ((N : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) * (β'⁻¹ * x * β').1 a b) ∈ Formalism.L2.Herm.intAf F E
      have h2 : s ((β'⁻¹ * x * β').1 a b) = (β⁻¹ * Formalism.UG.bc (s : _ →+* _) x * β).1 a b :=
        congrArg (fun g : GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) => g.1 a b) hs
      rw [map_mul, map_natCast, h2]
      exact hx a b
    · show c * ((N : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) * (β'⁻¹ * x * β').1 a b) = _
      rw [← mul_assoc, hc1, one_mul]
  · show (β' * (β'⁻¹ * x * β') * β'⁻¹).1 i j = x.1 i j
    group

theorem exists_compact_of_bd (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (N : ℕ) (hN : N ≠ 0) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ k ∈ GfC V,
      (∀ i j, (N : Lev.EAf D) * (β⁻¹ * Lev.finE V k * β).val i j ∈ OA D) → k ∈ C := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  let θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun ρ => θ₀ (tauE D ρ)
  have hθ : IsInfFam θ := fun ρ => hθ₀ _
  obtain ⟨C, hC, hCe⟩ := exists_compact_entries_bd β N hN
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C hC
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'
  refine ⟨K, hK, fun k h2 h1 => hKe k fun i j => hCe' _ (hCe (finHom V k) h1 i j) fun ρ => ?_⟩
  have hU : infMat D.sp.cm.sig V.gram (θ ρ) k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
    have h3 : (infHom V k).1 = 1 := congrArg Units.val (show infHom V k = 1 from h2)
    have h4 : infMat D.sp.cm.sig V.gram (θ ρ) k = ((infHom V k).1).map (θ ρ) := rfl
    rw [h4, h3, Matrix.map_one _ (map_zero _) (map_one _)]
    exact one_mem _
  exact _root_.entry_norm_bound_of_unitary hU i j

end GlobalTheory.ProdLevCompactC

open GlobalTheory.ProdLevCompactC in

theorem GlobalTheory.ProdLevCompactC.isCompact_levA : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))), (∀ w, ∃ C : Set (GL (Fin (n' w)) (Kw w.1)), IsCompact C ∧ (K w : Set (GL (Fin (n' w)) (Kw w.1))) ⊆ C) → IsOpen (((prodLev β P h K).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) → IsCompact ((Lev.levA V (prodLev β P h K) : Subgroup (GA D V)) : Set (GA D V)) := by
  intro D V β P n' h K hK ho
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨N, hN, hb⟩ := exists_bd V β P h K hK
  obtain ⟨C, hC, hCm⟩ := exists_compact_of_bd V β N hN
  refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC V).inter (Subgroup.isClosed_of_isOpen _ ho)) ?_
  rintro k ⟨hk1, hk2⟩
  refine hCm k hk1 fun i j => (mem_OA_iff _).2 fun Q => ?_
  exact hb _ hk2 (GlobalTheory.LevSplit.finE_mem_UA V k) Q i j
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.WtInterlaceC

open Finset GlobalTheory.SignedHC

def cnt (p : ℚ → Bool) (A B : Finset ℚ) : ℤ := ((A.filter fun x => p x).card : ℤ) - (B.filter fun x => p x).card

def IsUp (p : ℚ → Bool) : Prop := ∀ a b, a ≤ b → p a = true → p b = true

def Good (lo hi tot : ℤ) (A B : Finset ℚ) : Prop :=
  Disjoint A B ∧ (A.card : ℤ) - B.card = tot ∧ ∀ p, IsUp p → lo ≤ cnt p A B ∧ cnt p A B ≤ hi

theorem Good.union {lo1 hi1 t1 lo2 hi2 t2 lo hi : ℤ} {A1 B1 A2 B2 : Finset ℚ} (h1 : Good lo1 hi1 t1 A1 B1)
    (h2 : Good lo2 hi2 t2 A2 B2) (hsep : ∀ x ∈ A1 ∪ B1, ∀ y ∈ A2 ∪ B2, y < x) (hl1 : lo ≤ lo1) (hh1 : hi1 ≤ hi)
    (hl2 : lo ≤ t1 + lo2) (hh2 : t1 + hi2 ≤ hi) : Good lo hi (t1 + t2) (A1 ∪ A2) (B1 ∪ B2) := by
  obtain ⟨d1, c1, b1⟩ := h1
  obtain ⟨d2, c2, b2⟩ := h2
  have sAA : Disjoint A1 A2 := disjoint_left.2 fun x hx hx' =>
    lt_irrefl x (hsep x (mem_union_left _ hx) x (mem_union_left _ hx'))
  have sBB : Disjoint B1 B2 := disjoint_left.2 fun x hx hx' =>
    lt_irrefl x (hsep x (mem_union_right _ hx) x (mem_union_right _ hx'))
  have sAB : Disjoint A1 B2 := disjoint_left.2 fun x hx hx' =>
    lt_irrefl x (hsep x (mem_union_left _ hx) x (mem_union_right _ hx'))
  have sBA : Disjoint A2 B1 := disjoint_left.2 fun x hx hx' =>
    lt_irrefl x (hsep x (mem_union_right _ hx') x (mem_union_left _ hx))
  refine ⟨?_, ?_, fun p hp => ?_⟩
  · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨d1, sAB⟩, ⟨sBA, d2⟩⟩
  · rw [card_union_of_disjoint sAA, card_union_of_disjoint sBB]
    push_cast
    linarith
  · have e : cnt p (A1 ∪ A2) (B1 ∪ B2) = cnt p A1 B1 + cnt p A2 B2 := by
      simp only [cnt, filter_union]
      rw [card_union_of_disjoint (disjoint_filter_filter sAA), card_union_of_disjoint (disjoint_filter_filter sBB)]
      push_cast
      ring
    rw [e]
    by_cases hY : ∃ y ∈ A2 ∪ B2, p y = true
    · obtain ⟨y, hy, hpy⟩ := hY
      have hX : ∀ x ∈ A1 ∪ B1, p x = true := fun x hx => hp y x (hsep x hx y hy).le hpy
      have e1 : cnt p A1 B1 = t1 := by
        rw [cnt, filter_true_of_mem fun x hx => hX x (mem_union_left _ hx),
          filter_true_of_mem fun x hx => hX x (mem_union_right _ hx), c1]
      rw [e1]
      have := b2 p hp
      constructor <;> linarith [this.1, this.2]
    · push_neg at hY
      have e2 : cnt p A2 B2 = 0 := by
        rw [cnt, filter_false_of_mem fun x hx => by simpa using hY x (mem_union_left _ hx),
          filter_false_of_mem fun x hx => by simpa using hY x (mem_union_right _ hx)]
        simp
      rw [e2, add_zero]
      have := b1 p hp
      constructor <;> linarith [this.1, this.2]

theorem good_pair {x y : ℚ} (h : x < y) : Good (-1) 0 0 {x} {y} := by
  refine ⟨disjoint_singleton.2 h.ne, by simp, fun p hp => ?_⟩
  simp only [cnt, filter_singleton]
  by_cases hx : p x = true
  · have hy := hp x y h.le hx
    simp [hx, hy]
  · by_cases hy : p y = true <;> simp [hx, hy]

theorem good_single (x : ℚ) : Good 0 1 1 {x} ∅ := by
  refine ⟨disjoint_empty_right _, by simp, fun p _ => ?_⟩
  simp only [cnt, filter_singleton, filter_empty, card_empty]
  by_cases hx : p x = true <;> simp [hx]

theorem good_congr {lo hi t : ℤ} {A B A' B' : Finset ℚ} (h : Good lo hi t A B) (hA : A = A') (hB : B = B') :
    Good lo hi t A' B' := hA ▸ hB ▸ h

theorem block_succ_top (c : ℚ) (n : ℕ) : TPar.block c (n + 1) = {c + (n : ℚ) / 2} ∪ TPar.block (c - 1 / 2) n := by
  ext x
  simp only [mem_union, mem_singleton, mem_block]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases Nat.eq_zero_or_pos a with rfl | h
    · left; push_cast; ring
    · right; exact ⟨a - 1, by omega, by rw [Nat.cast_sub h]; push_cast; ring⟩
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨0, by omega, by push_cast; ring⟩
    · exact ⟨a + 1, by omega, by push_cast; ring⟩

theorem block_succ_bot (c : ℚ) (n : ℕ) : TPar.block c (n + 1) = TPar.block (c + 1 / 2) n ∪ {c - (n : ℚ) / 2} := by
  ext x
  simp only [mem_union, mem_singleton, mem_block]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases (Nat.lt_succ_iff.1 ha).eq_or_lt with rfl | h
    · right; push_cast; ring
    · left; exact ⟨a, h, by push_cast; ring⟩
  · rintro (⟨a, ha, rfl⟩ | rfl)
    · exact ⟨a, by omega, by push_cast; ring⟩
    · exact ⟨n, by omega, by push_cast; ring⟩

theorem block_le {c x : ℚ} {n : ℕ} (h : x ∈ TPar.block c n) : x ≤ c + ((n : ℚ) - 1) / 2 := by
  obtain ⟨a, -, rfl⟩ := mem_block.1 h
  have : (0 : ℚ) ≤ a := by positivity
  linarith

theorem block_ge {c x : ℚ} {n : ℕ} (h : x ∈ TPar.block c n) : c - ((n : ℚ) - 1) / 2 ≤ x := by
  obtain ⟨a, ha, rfl⟩ := mem_block.1 h
  have : (a : ℚ) + 1 ≤ n := by exact_mod_cast ha
  linarith

theorem good_blocks : ∀ (n : ℕ) (c : ℚ), Good (-1) 0 0 (TPar.block c n) (TPar.block (c + 1 / 2) n) := by
  intro n
  induction n with
  | zero => intro c; exact ⟨by simp [TPar.block], by simp [TPar.block], fun p _ => by simp [cnt, TPar.block]⟩
  | succ n ih =>
    intro c
    have h := ih (c - 1 / 2)
    rw [sub_add_cancel] at h
    have e1 := block_succ_top c n
    have e2 := block_succ_top (c + 1 / 2) n
    rw [add_sub_cancel_right] at e2
    rw [e1, e2]
    have := (good_pair (x := c + (n : ℚ) / 2) (y := c + 1 / 2 + (n : ℚ) / 2) (by linarith)).union h ?_
      (le_refl _) (le_refl _) (by norm_num) (by norm_num)
    · simpa using this
    · intro x hx y hy
      simp only [mem_union, mem_singleton] at hx
      have hy' : y ≤ c + ((n : ℚ) - 1) / 2 := by
        rcases mem_union.1 hy with hy | hy
        · have := block_le hy; linarith
        · exact block_le hy
      rcases hx with rfl | rfl <;> linarith

end GlobalTheory.WtInterlaceC

namespace GlobalTheory.WtInterlaceC

open Finset GlobalTheory.SignedHC

theorem good_empty : Good (-1) 0 0 ∅ ∅ := ⟨disjoint_empty_left _, by simp, fun p _ => by simp [cnt]⟩

theorem good_family (A B : ℕ → Finset ℚ) (lo : ℕ) : ∀ n : ℕ,
    (∀ i, lo ≤ i → i < lo + n → Good (-1) 0 0 (A i) (B i)) →
    (∀ i j, lo ≤ i → i < j → j < lo + n → ∀ x ∈ A i ∪ B i, ∀ y ∈ A j ∪ B j, y < x) →
    Good (-1) 0 0 ((Ico lo (lo + n)).biUnion A) ((Ico lo (lo + n)).biUnion B) := by
  intro n
  induction n with
  | zero => intro _ _; simpa using good_empty
  | succ n ih =>
    intro hg hsep
    have e : Ico lo (lo + (n + 1)) = insert (lo + n) (Ico lo (lo + n)) := by
      ext i; simp only [mem_insert, mem_Ico]; omega
    rw [e, biUnion_insert, biUnion_insert, union_comm (A (lo + n)), union_comm (B (lo + n))]
    have h1 := ih (fun i h1 h2 => hg i h1 (by omega)) (fun i j h1 h2 h3 => hsep i j h1 h2 (by omega))
    have h2 := hg (lo + n) (by omega) (by omega)
    have := h1.union h2 ?_ (le_refl _) (le_refl _) (by norm_num) (by norm_num)
    · simpa using this
    · intro x hx y hy
      have hx' : x ∈ (Ico lo (lo + n)).biUnion (fun i => A i ∪ B i) := by
        rw [biUnion_union]; exact hx
      obtain ⟨i, hi, hx''⟩ := mem_biUnion.1 hx'
      rw [mem_Ico] at hi
      exact hsep i (lo + n) hi.1 hi.2 (by omega) x hx'' y hy

theorem cnt_decide (P : ℚ → Prop) [DecidablePred P] (A B : Finset ℚ) :
    cnt (fun z => decide (P z)) A B = ((A.filter P).card : ℤ) - (B.filter P).card := by
  simp [cnt]

theorem isUp_le (q : ℚ) : IsUp (fun z => decide (q ≤ z)) := fun a b h ha => by
  simp only [decide_eq_true_eq] at ha ⊢; linarith

theorem isUp_lt (q : ℚ) : IsUp (fun z => decide (q < z)) := fun a b h ha => by
  simp only [decide_eq_true_eq] at ha ⊢; linarith

theorem strictInterlace_of_good {A B : Finset ℚ} (h : Good 0 1 1 A B) : StrictInterlace A B := by
  obtain ⟨hd, hc, hb⟩ := h
  rw [strictInterlace_iff]
  refine ⟨hd, card_pos.1 (by omega), fun y hy => ?_, fun y hy => ?_, fun x hx y hy hxy hz => ?_⟩
  · by_contra hne
    push_neg at hne
    have h1 : 0 ≤ ((A.filter fun z => y ≤ z).card : ℤ) - (B.filter fun z => y ≤ z).card := by
      have := (hb _ (isUp_le y)).1; rw [cnt_decide] at this; exact this
    have e1 : A.filter (fun z => y ≤ z) = ∅ := filter_eq_empty_iff.2 fun z hz h' =>
      disjoint_left.1 hd (le_antisymm (hne z hz) h' ▸ hz) hy
    have e2 : 1 ≤ (B.filter (fun z => y ≤ z)).card := card_pos.2 ⟨y, mem_filter.2 ⟨hy, le_rfl⟩⟩
    rw [e1, card_empty] at h1
    omega
  · by_contra hne
    push_neg at hne
    have h1 : ((A.filter fun z => y < z).card : ℤ) - (B.filter fun z => y < z).card ≤ 1 := by
      have := (hb _ (isUp_lt y)).2; rw [cnt_decide] at this; exact this
    have e1 : A.filter (fun z => y < z) = A := filter_true_of_mem fun z hz =>
      lt_of_le_of_ne (hne z hz) fun e => disjoint_left.1 hd (e ▸ hz) hy
    have e2 : B.filter (fun z => y < z) ⊆ B.erase y := fun z hz => by
      rw [mem_filter] at hz; exact mem_erase.2 ⟨hz.2.ne', hz.1⟩
    have e3 := card_le_card e2
    rw [card_erase_of_mem hy] at e3
    rw [e1] at h1
    have : 1 ≤ B.card := card_pos.2 ⟨y, hy⟩
    omega
  · have hne : x ≠ y := hxy.ne'
    have split : ∀ S : Finset ℚ, S ⊆ A ∪ B → ((S.filter fun z => y ≤ z).card : ℤ) =
        (S.filter fun z => x < z).card + (if x ∈ S then 1 else 0) + (if y ∈ S then 1 else 0) := by
      intro S hS
      have e : S.filter (fun z => y ≤ z) = (S.filter fun z => x < z) ∪ ((S.filter fun z => z = x) ∪ S.filter fun z => z = y) := by
        ext z
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨hzS, hyz⟩
          rcases hyz.eq_or_lt with rfl | hyz
          · exact Or.inr (Or.inr ⟨hzS, rfl⟩)
          · have : ¬ z < x := fun h' => hz z (hS hzS) ⟨hyz, h'⟩
            rcases (not_lt.1 this).eq_or_lt with rfl | h'
            · exact Or.inr (Or.inl ⟨hzS, rfl⟩)
            · exact Or.inl ⟨hzS, h'⟩
        · rintro (⟨hzS, h'⟩ | ⟨hzS, rfl⟩ | ⟨hzS, rfl⟩)
          · exact ⟨hzS, by linarith⟩
          · exact ⟨hzS, hxy.le⟩
          · exact ⟨hzS, le_rfl⟩
      have d1 : Disjoint (S.filter fun z => z = x) (S.filter fun z => z = y) :=
        disjoint_filter.2 fun z _ h1 h2 => hne (h1 ▸ h2 ▸ rfl)
      have d2 : Disjoint (S.filter fun z => x < z) ((S.filter fun z => z = x) ∪ S.filter fun z => z = y) := by
        rw [disjoint_union_right]
        exact ⟨disjoint_filter.2 fun z _ h1 h2 => by rw [h2] at h1; exact lt_irrefl _ h1,
          disjoint_filter.2 fun z _ h1 h2 => by rw [h2] at h1; linarith⟩
      rw [e, card_union_of_disjoint d2, card_union_of_disjoint d1, filter_eq' S x, filter_eq' S y]
      split_ifs <;> simp only [card_singleton, card_empty] <;> push_cast <;> ring
    have hA := split A subset_union_left
    have hB := split B subset_union_right
    have h1 : 0 ≤ ((A.filter fun z => y ≤ z).card : ℤ) - (B.filter fun z => y ≤ z).card ∧
        ((A.filter fun z => y ≤ z).card : ℤ) - (B.filter fun z => y ≤ z).card ≤ 1 := by
      have := hb _ (isUp_le y); rw [cnt_decide] at this; exact this
    have h2 : 0 ≤ ((A.filter fun z => x < z).card : ℤ) - (B.filter fun z => x < z).card ∧
        ((A.filter fun z => x < z).card : ℤ) - (B.filter fun z => x < z).card ≤ 1 := by
      have := hb _ (isUp_lt x); rw [cnt_decide] at this; exact this
    have hxAB := mem_union.1 hx
    have hyAB := mem_union.1 hy
    constructor
    · intro hxA hyA
      have hxB : x ∉ B := disjoint_left.1 hd hxA
      have hyB : y ∉ B := disjoint_left.1 hd hyA
      rw [if_pos hxA, if_pos hyA] at hA
      rw [if_neg hxB, if_neg hyB] at hB
      omega
    · intro hyA
      by_contra hxA
      have hxB : x ∈ B := hxAB.resolve_left hxA
      have hyB : y ∈ B := hyAB.resolve_left hyA
      rw [if_neg hxA, if_neg hyA] at hA
      rw [if_pos hxB, if_pos hyB] at hB
      omega

end GlobalTheory.WtInterlaceC

namespace GlobalTheory.WtInterlaceC

open Finset GlobalTheory.SignedHC

theorem good_CB (c a : ℚ) (n : ℕ) (ha : a < c - (n : ℚ) / 2) :
    Good (-1) 0 0 (TPar.block c n ∪ {a}) (TPar.block c (n + 1)) := by
  rw [block_succ_bot]
  have h := (good_blocks n c).union (good_pair ha) ?_ (le_refl _) (le_refl _) (by norm_num) (by norm_num)
  · rwa [add_zero] at h
  · intro x hx y hy
    simp only [mem_union, mem_singleton] at hy
    have : c - (n : ℚ) / 2 < x := by
      rcases mem_union.1 hx with hx | hx
      · have := block_ge hx; linarith
      · have := block_ge hx; linarith
    rcases hy with rfl | rfl <;> linarith

theorem good_MB (e b : ℚ) (t : ℕ) (hb : e + (t : ℚ) / 2 < b) :
    Good (-1) 0 0 (TPar.block e (t + 1)) ({b} ∪ TPar.block e t) := by
  rw [block_succ_top]
  have h2 := good_blocks t (e - 1 / 2)
  rw [sub_add_cancel] at h2
  have h := (good_pair hb).union h2 ?_ (le_refl _) (le_refl _) (by norm_num) (by norm_num)
  · rwa [add_zero] at h
  · intro x hx y hy
    simp only [mem_union, mem_singleton] at hx
    have : y ≤ e + ((t : ℚ) - 1) / 2 := by
      rcases mem_union.1 hy with hy | hy
      · have := block_le hy; linarith
      · exact block_le hy
    rcases hx with rfl | rfl <;> linarith

end GlobalTheory.WtInterlaceC

namespace GlobalTheory.WtInterlaceC

open Finset GlobalTheory.SignedHC GlobalTheory.FunObj GlobalTheory.ChiGrid

section Num

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

local notation "Γ" => num D C τ

theorem good_U {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) :
    Good (-1) 0 0 ((Γ).blockC' i ∪ {(Γ).a i}) ((Γ).blockC i) := by
  have hs : 1 ≤ (Γ).s := (odd_sLen D).pos
  have key := good_CB ((Γ).cen i : ℚ) ((Γ).a i) ((Γ).s - 1) ?_
  · rw [Nat.sub_add_cancel hs] at key
    exact key
  · have hmem : ((Γ).cen i : ℚ) - (((Γ).s - 1 : ℕ) : ℚ) / 2 ∈ (Γ).blockC i := by
      refine mem_block.2 ⟨(Γ).s - 1, by omega, ?_⟩
      rw [Nat.cast_sub hs]; push_cast; ring
    exact (blockC_bd D C τ h1 h2 hmem).1

theorem one_pow_not_mem_height_one_asIdeal {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) :
    Good (-1) 0 0 ((Γ).blockMPlus l) ({-((Γ).b l : ℚ)} ∪ (Γ).blockM l) := by
  refine good_MB (-((Γ).e l : ℚ)) (-((Γ).b l : ℚ)) (Γ).t ?_
  have := num_be D C τ h1 h2
  have e : ((Γ).t : ℚ) = D.R.t := rfl
  rw [e]; linarith

theorem lb_U {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) {x : ℚ} (hx : x ∈ ((Γ).blockC' i ∪ {(Γ).a i}) ∪ (Γ).blockC i) :
    (Γ).a i ≤ x := by
  rcases mem_union.1 hx with hx | hx
  · rcases mem_union.1 hx with hx | hx
    · exact (blockC'_between (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C) h1 h2 hx).1.le
    · rw [mem_singleton.1 hx]
  · exact (blockC_bd D C τ h1 h2 hx).1.le

theorem ub_U {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) {x : ℚ} (hx : x ∈ ((Γ).blockC' i ∪ {(Γ).a i}) ∪ (Γ).blockC i) :
    x < (Γ).a i + (Γ).ga := by
  have hga : (0 : ℚ) < (Γ).ga := by
    have : 0 < (Γ).ga := lt_of_le_of_lt (Nat.zero_le _) (sLen_lt_gap D C)
    exact_mod_cast this
  rcases mem_union.1 hx with hx | hx
  · rcases mem_union.1 hx with hx | hx
    · exact (blockC'_between (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C) h1 h2 hx).2
    · rw [mem_singleton.1 hx]; linarith
  · exact (blockC_bd D C τ h1 h2 hx).2

theorem chiGrid_row_entries_lower_bound {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) {x : ℚ} (hx : x ∈ (Γ).blockMPlus l ∪ ({-((Γ).b l : ℚ)} ∪ (Γ).blockM l)) :
    -((Γ).e l : ℚ) - (D.R.t : ℚ) / 2 ≤ x := by
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  rcases mem_union.1 hx with hx | hx
  · exact (blockMPlus_bd D C τ hx).1
  · rcases mem_union.1 hx with hx | hx
    · rw [mem_singleton.1 hx]; linarith [num_be D C τ h1 h2]
    · linarith [(blockM_bd D C τ hx).1]

theorem chiGrid_row_entries_upper_bound {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) {x : ℚ} (hx : x ∈ (Γ).blockMPlus l ∪ ({-((Γ).b l : ℚ)} ∪ (Γ).blockM l)) :
    x ≤ -((Γ).b l : ℚ) := by
  have hbe := num_be D C τ h1 h2
  rcases mem_union.1 hx with hx | hx
  · linarith [(blockMPlus_bd D C τ hx).2]
  · rcases mem_union.1 hx with hx | hx
    · rw [mem_singleton.1 hx]
    · linarith [(blockM_bd D C τ hx).2]

theorem good_top_grid : Good 0 1 1 ((Γ).weightX D.R.m) (entries ((Γ).parD D.R.m D.R.m)) := by
  have hm : (Γ).m = D.R.m := rfl
  have hk : (Γ).k = D.R.k := rfl
  have hk2 : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have FU := good_family (fun i => (Γ).blockC' i ∪ {(Γ).a i}) (fun i => (Γ).blockC i) 1 D.R.m
    (fun i h1 h2 => good_U D C τ h1 (by omega)) fun i j h1 h2 h3 x hx y hy =>
      lt_of_lt_of_le (ub_U D C τ (by omega) (by omega) hy)
        ((a_add_le (G := Γ) h2).trans (lb_U D C τ h1 (by omega) hx))
  have FV := good_family (fun j => {(Γ).vHalf j}) (fun j => {((Γ).v j : ℚ)}) 2 (D.R.k - 1)
    (fun j _ _ => good_pair (by unfold GridData.vHalf; linarith)) fun i j h1 h2 h3 x hx y hy => by
      have hv : (Γ).v j < (Γ).v i := (Γ).v_anti i j h1 h2 (by rw [hk]; omega)
      have hv' : ((Γ).v j : ℚ) + 1 ≤ (Γ).v i := by exact_mod_cast hv
      simp only [mem_union, mem_singleton, GridData.vHalf] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> linarith
  have FW := good_family (fun l => (Γ).blockMPlus l) (fun l => {-((Γ).b l : ℚ)} ∪ (Γ).blockM l) 1 D.R.m
    (fun l h1 h2 => one_pow_not_mem_height_one_asIdeal D C τ h1 (by omega)) fun i j h1 h2 h3 x hx y hy => by
      have e1 := num_eb D C τ (l := i) h1 (by omega)
      have e2 := num_b_le D C τ (i := i + 1) (j := j) (by omega) h2 (by omega)
      have e3 := chiGrid_row_entries_lower_bound D C τ h1 (by omega) hx
      have e4 := chiGrid_row_entries_upper_bound D C τ (by omega) (by omega) hy
      have ht : (0 : ℚ) ≤ D.R.t := by positivity
      linarith
  have memU : ∀ y ∈ (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC' i ∪ {(Γ).a i}) ∪
      (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC i), ∃ i, 1 ≤ i ∧ i ≤ D.R.m ∧
        y ∈ ((Γ).blockC' i ∪ {(Γ).a i}) ∪ (Γ).blockC i := by
    intro y hy
    rw [← biUnion_union] at hy
    obtain ⟨i, hi, hy⟩ := mem_biUnion.1 hy
    rw [mem_Ico] at hi
    exact ⟨i, hi.1, by omega, hy⟩
  have memV : ∀ y ∈ (Ico 2 (2 + (D.R.k - 1))).biUnion (fun j => ({(Γ).vHalf j} : Finset ℚ)) ∪
      (Ico 2 (2 + (D.R.k - 1))).biUnion (fun j => ({((Γ).v j : ℚ)} : Finset ℚ)), ∃ j, 2 ≤ j ∧ j ≤ D.R.k ∧
        (y = (Γ).vHalf j ∨ y = (Γ).v j) := by
    intro y hy
    rw [← biUnion_union] at hy
    obtain ⟨j, hj, hy⟩ := mem_biUnion.1 hy
    rw [mem_Ico] at hj
    simp only [mem_union, mem_singleton] at hy
    exact ⟨j, hj.1, by omega, hy⟩
  have memW : ∀ y ∈ (Ico 1 (1 + D.R.m)).biUnion (fun l => (Γ).blockMPlus l) ∪
      (Ico 1 (1 + D.R.m)).biUnion (fun l => {-((Γ).b l : ℚ)} ∪ (Γ).blockM l), ∃ l, 1 ≤ l ∧ l ≤ D.R.m ∧
        y ∈ (Γ).blockMPlus l ∪ ({-((Γ).b l : ℚ)} ∪ (Γ).blockM l) := by
    intro y hy
    rw [← biUnion_union] at hy
    obtain ⟨l, hl, hy⟩ := mem_biUnion.1 hy
    rw [mem_Ico] at hl
    exact ⟨l, hl.1, by omega, hy⟩
  have T1 := (good_single ((Γ).a 0)).union FU (fun x hx y hy => by
      obtain ⟨i, h1, h2, hy⟩ := memU y hy
      have hx' : x = (Γ).a 0 := by simpa using hx
      rw [hx']
      exact lt_of_lt_of_le (ub_U D C τ h1 h2 hy) (a_add_le (G := Γ) (by omega)))
    (le_refl _) (le_refl _) (by norm_num) (by norm_num)
  have lb1 : ∀ x ∈ ({(Γ).a 0} ∪ (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC' i ∪ {(Γ).a i})) ∪
      (∅ ∪ (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC i)), (Γ).a (Γ).m ≤ x := by
    intro x hx
    simp only [empty_union] at hx
    rcases mem_union.1 hx with hx | hx
    · rcases mem_union.1 hx with hx | hx
      · rw [mem_singleton.1 hx]; exact a_le D C τ (Nat.zero_le _)
      · obtain ⟨i, h1, h2, hx⟩ := memU x (mem_union_left _ hx)
        exact (a_le D C τ (by rw [hm]; exact h2)).trans (lb_U D C τ h1 h2 hx)
    · obtain ⟨i, h1, h2, hx⟩ := memU x (mem_union_right _ hx)
      exact (a_le D C τ (by rw [hm]; exact h2)).trans (lb_U D C τ h1 h2 hx)
  have T2 := T1.union FV (fun x hx y hy => by
      obtain ⟨j, h1, h2, hy⟩ := memV y hy
      have := v_lt_a D C τ h1 h2
      have := lb1 x hx
      rcases hy with rfl | rfl
      · unfold GridData.vHalf; linarith
      · linarith)
    (le_refl _) (le_refl _) (by norm_num) (by norm_num)
  have hb1 : -((Γ).b 1 : ℚ) < (Γ).a (Γ).m := low_lt_a D C τ le_rfl
  have T3 := T2.union FW (fun x hx y hy => by
      obtain ⟨l, h1, h2, hy⟩ := memW y hy
      have e1 := chiGrid_row_entries_upper_bound D C τ h1 h2 hy
      have e2 := num_b_le D C τ (i := 1) (j := l) le_rfl h1 h2
      have lx : -((Γ).b 1 : ℚ) < x := by
        rcases mem_union.1 hx with hx | hx
        · rcases mem_union.1 hx with hx | hx
          · linarith [lb1 x (mem_union_left _ hx)]
          · obtain ⟨j, h1, h2, hx⟩ := memV x (mem_union_left _ hx)
            have := num_cloud D C τ h1 h2
            rcases hx with rfl | rfl
            · unfold GridData.vHalf; linarith
            · linarith
        · rcases mem_union.1 hx with hx | hx
          · linarith [lb1 x (mem_union_right _ hx)]
          · obtain ⟨j, h1, h2, hx⟩ := memV x (mem_union_right _ hx)
            have := num_cloud D C τ h1 h2
            rcases hx with rfl | rfl
            · unfold GridData.vHalf; linarith
            · linarith
      linarith)
    (le_refl _) (le_refl _) (by norm_num) (by norm_num)
  have hA : {(Γ).a 0} ∪ (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC' i ∪ {(Γ).a i}) ∪
      (Ico 2 (2 + (D.R.k - 1))).biUnion (fun j => ({(Γ).vHalf j} : Finset ℚ)) ∪
      (Ico 1 (1 + D.R.m)).biUnion (fun l => (Γ).blockMPlus l) = (Γ).weightX D.R.m := by
    ext x
    simp only [mem_union, mem_singleton, mem_biUnion, mem_Ico, GridData.mem_weightX, GridData.mem_tops,
      GridData.mem_cloudHalf, hm, hk]
    constructor
    · rintro (((hx | ⟨i, ⟨h1, h2⟩, hx | hx⟩) | ⟨j, ⟨h1, h2⟩, hx⟩) | ⟨l, ⟨h1, h2⟩, hx⟩)
      · exact Or.inl ⟨0, Nat.zero_le _, hx⟩
      · exact Or.inr (Or.inr (Or.inl ⟨i, h1, by omega, hx⟩))
      · exact Or.inl ⟨i, by omega, hx⟩
      · exact Or.inr (Or.inl ⟨j, h1, by omega, hx⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨l, h1, by omega, hx⟩))
    · rintro (⟨i, hi, hx⟩ | ⟨j, h1, h2, hx⟩ | ⟨i, h1, h2, hx⟩ | ⟨l, h1, h2, hx⟩)
      · rcases Nat.eq_zero_or_pos i with rfl | h
        · exact Or.inl (Or.inl (Or.inl hx))
        · exact Or.inl (Or.inl (Or.inr ⟨i, ⟨h, by omega⟩, Or.inr hx⟩))
      · exact Or.inl (Or.inr ⟨j, ⟨h1, by omega⟩, hx⟩)
      · exact Or.inl (Or.inl (Or.inr ⟨i, ⟨h1, by omega⟩, Or.inl hx⟩))
      · exact Or.inr ⟨l, ⟨h1, by omega⟩, hx⟩
  have hB : ∅ ∪ (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC i) ∪
      (Ico 2 (2 + (D.R.k - 1))).biUnion (fun j => ({((Γ).v j : ℚ)} : Finset ℚ)) ∪
      (Ico 1 (1 + D.R.m)).biUnion (fun l => {-((Γ).b l : ℚ)} ∪ (Γ).blockM l) = entries ((Γ).parD D.R.m D.R.m) := by
    ext x
    rw [GridData.entries_parD]
    simp only [empty_union, mem_union, mem_singleton, mem_biUnion, mem_Ico, mem_Icc, GridData.mem_cloud,
      GridData.mem_lows, hm, hk]
    constructor
    · rintro ((⟨i, ⟨h1, h2⟩, hx⟩ | ⟨j, ⟨h1, h2⟩, hx⟩) | ⟨l, ⟨h1, h2⟩, hx | hx⟩)
      · exact Or.inr ⟨i, ⟨by omega, by omega⟩, hx⟩
      · exact Or.inl (Or.inl (Or.inl ⟨j, h1, by omega, hx⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨l, h1, by omega, hx⟩))
      · exact Or.inl (Or.inr ⟨l, ⟨h1, by omega⟩, hx⟩)
    · rintro (((⟨j, h1, h2, hx⟩ | ⟨l, h1, h2, hx⟩) | ⟨l, ⟨h1, h2⟩, hx⟩) | ⟨i, ⟨h1, h2⟩, hx⟩)
      · exact Or.inl (Or.inr ⟨j, ⟨h1, by omega⟩, hx⟩)
      · exact Or.inr ⟨l, ⟨h1, by omega⟩, Or.inl hx⟩
      · exact Or.inr ⟨l, ⟨h1, by omega⟩, Or.inr hx⟩
      · exact Or.inl (Or.inl ⟨i, ⟨by omega, by omega⟩, hx⟩)
  exact good_congr T3 hA hB

end Num

end GlobalTheory.WtInterlaceC

namespace GlobalTheory.WtInterlaceC

open Finset GlobalTheory.SignedHC GlobalTheory.FunObj GlobalTheory.ChiGrid

theorem interlace_wtOf {N n : ℕ} (hN : N = n + 1) {A B : Finset ℚ} (hA : A.card = N) (hB : B.card = n)
    (hAc : InCoset (((N : ℚ) - 1) / 2) A) (hBc : InCoset (((n : ℚ) - 1) / 2) B) (hSI : StrictInterlace A B) :
    Formalism.L2.Col.Br.Interlace hN (wtOf N A) (wtOf n B) := by
  subst hN
  have key := (strictInterlace_iff_descEnum hA hB).1 hSI
  intro i
  have eA : ∀ j, ((wtOf (n + 1) A).w j : ℚ) = descEnum A hA j - ((((n + 1 : ℕ) : ℚ) - 1) / 2 - ((j : ℕ) : ℚ)) :=
    fun j => wtOf_cast hA hAc j
  have eB : ∀ j, ((wtOf n B).w j : ℚ) = descEnum B hB j - (((n : ℚ) - 1) / 2 - ((j : ℕ) : ℚ)) :=
    fun j => wtOf_cast hB hBc j
  have s1 : Formalism.L2.Col.Br.iS (rfl : n + 1 = n + 1) i = i.succ := Fin.ext rfl
  have s2 : Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) i = i.castSucc := Fin.ext rfl
  have h1 := eA i.succ
  have h2 := eA i.castSucc
  have h3 := eB i
  obtain ⟨k1, k2⟩ := key i
  simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
  push_cast at h1 h2
  unfold Formalism.L2.Col.Br.aBr Formalism.L2.Col.Br.bBr
  rw [s1, s2]
  constructor
  · have : (-1 : ℚ) < (((wtOf n B).w i - (wtOf (n + 1) A).w i.succ : ℤ) : ℚ) := by
      push_cast; rw [h1, h3]; linarith
    have : (-1 : ℤ) < (wtOf n B).w i - (wtOf (n + 1) A).w i.succ := by exact_mod_cast this
    omega
  · have : (-1 : ℚ) < (((wtOf (n + 1) A).w i.castSucc - (wtOf n B).w i : ℤ) : ℚ) := by
      push_cast; rw [h2, h3]; linarith
    have : (-1 : ℤ) < (wtOf (n + 1) A).w i.castSucc - (wtOf n B).w i := by exact_mod_cast this
    omega

theorem descEnum_last {m : ℕ} {E : Finset ℚ} (h : E.card = m) (hm : 0 < m) {z : ℚ} (hz : z ∈ E)
    (hmin : ∀ y ∈ E, z ≤ y) : descEnum E h ⟨m - 1, by omega⟩ = z := by
  apply le_antisymm
  · rw [← image_descEnum E h] at hz
    obtain ⟨j, -, hj⟩ := mem_image.1 hz
    rw [← hj]
    exact (strictAnti_descEnum E h).antitone (Fin.mk_le_mk.2 (by have := j.2; omega))
  · exact hmin _ (descEnum_mem E h _)

theorem sameShift_wtOf {N n : ℕ} (hN : N = n + 1) (hn : 0 < n) {A B : Finset ℚ} (hA : A.card = N) (hB : B.card = n)
    (hAc : InCoset (((N : ℚ) - 1) / 2) A) (hBc : InCoset (((n : ℚ) - 1) / 2) B) {x : ℚ} (hxA : x ∈ A)
    (hAm : ∀ y ∈ A, x ≤ y) (hxB : x + 1 / 2 ∈ B) (hBm : ∀ y ∈ B, x + 1 / 2 ≤ y) :
    Formalism.L2.Col.Br.SameShift (wtOf N A) (wtOf n B) := by
  subst hN
  unfold Formalism.L2.Col.Br.SameShift DomWeight.detShift
  rw [dif_pos hn, dif_pos (Nat.succ_pos n)]
  have e1 := wtOf_cast hB hBc ⟨n - 1, by omega⟩
  have e2 := wtOf_cast hA hAc ⟨n + 1 - 1, by omega⟩
  simp only [highestWeight] at e1 e2
  rw [descEnum_last hB hn hxB hBm] at e1
  rw [descEnum_last hA (Nat.succ_pos n) hxA hAm] at e2
  have : (((wtOf n B).w ⟨n - 1, by omega⟩ : ℤ) : ℚ) = (((wtOf (n + 1) A).w ⟨n + 1 - 1, by omega⟩ : ℤ) : ℚ) := by
    rw [e1, e2]
    rw [Nat.cast_sub hn]
    push_cast
    ring
  exact_mod_cast this

end GlobalTheory.WtInterlaceC

namespace GlobalTheory.WtInterlaceC

open Finset GlobalTheory.SignedHC GlobalTheory.FunObj GlobalTheory.ChiGrid

section Min

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

local notation "Γ" => num D C τ

theorem low_mem_weightX : -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 ∈ (Γ).weightX D.R.m := by
  have hm2 := D.R.two_le_m
  have et : ((Γ).t : ℚ) = D.R.t := rfl
  refine GridData.mem_weightX.2 (Or.inr (Or.inr (Or.inr ⟨D.R.m, by omega, le_rfl, mem_block.2 ⟨(Γ).t, by omega, ?_⟩⟩)))
  push_cast
  rw [et]
  ring

theorem min_weightX {y : ℚ} (hy : y ∈ (Γ).weightX D.R.m) : -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 ≤ y := by
  have hm2 := D.R.two_le_m
  have hz := low_mem_weightX D C τ
  obtain ⟨j, hj⟩ : ∃ j, D.R.m = j + 1 := ⟨D.R.m - 1, by omega⟩
  have hz' : -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 ∈ (Γ).blockMPlus D.R.m := by
    have et : ((Γ).t : ℚ) = D.R.t := rfl
    refine mem_block.2 ⟨(Γ).t, by omega, ?_⟩
    push_cast
    rw [et]
    ring
  rw [hj] at hy hz' ⊢
  rw [GridData.weightX_succ] at hy
  rcases mem_union.1 hy with hy | hy
  · exact (weightX_above D C τ (j := j) (by omega) hy hz').le
  · exact (blockMPlus_bd D C τ hy).1

theorem half_mem_parD : -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 + 1 / 2 ∈ entries ((Γ).parD D.R.m D.R.m) := by
  have hm2 := D.R.two_le_m
  have ht := D.R.t_odd.pos
  have et : ((Γ).t : ℚ) = D.R.t := rfl
  have hmem : -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 + 1 / 2 ∈ (Γ).blockM D.R.m := by
    refine mem_block.2 ⟨(Γ).t - 1, by show D.R.t - 1 < D.R.t; omega, ?_⟩
    rw [Nat.cast_sub (show 1 ≤ (Γ).t from ht), et]
    ring
  rw [GridData.entries_parD]
  exact mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨D.R.m, mem_Icc.2 ⟨by omega, le_rfl⟩, hmem⟩))

theorem min_parD {y : ℚ} (hy : y ∈ entries ((Γ).parD D.R.m D.R.m)) :
    -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 + 1 / 2 ≤ y := by
  have hm2 := D.R.two_le_m
  have hm : (Γ).m = D.R.m := rfl
  have hbe := num_be D C τ (l := D.R.m) (by omega) le_rfl
  have hbm := num_b_le D C τ (i := 1) (j := D.R.m) le_rfl (by omega) le_rfl
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  rw [GridData.entries_parD] at hy
  rcases mem_union.1 hy with hy | hy
  · rcases mem_union.1 hy with hy | hy
    · rcases mem_union.1 hy with hy | hy
      · have := (cloud_gt D C τ hy).1
        linarith
      · obtain ⟨l, h1, h2, rfl⟩ := GridData.mem_lows.1 hy
        have := num_b_le D C τ (i := l) (j := D.R.m) h1 (by rw [← hm]; exact h2) le_rfl
        linarith
    · obtain ⟨l, hl, hy⟩ := mem_biUnion.1 hy
      simp only [mem_Icc, hm] at hl
      have e1 := (blockM_bd D C τ hy).1
      have e2 : ((Γ).e l : ℚ) ≤ (Γ).e D.R.m := by
        rcases hl.2.eq_or_lt with h | h
        · rw [h]
        · linarith [num_e_lt D C τ hl.1 h le_rfl]
      linarith
  · obtain ⟨l, hl, hy⟩ := mem_biUnion.1 hy
    simp only [mem_Icc, hm] at hl
    have e1 := (blockC_bd D C τ (by omega) hl.2 hy).1
    have e2 := a_le D C τ (i := l) (j := (Γ).m) (by rw [hm]; exact hl.2)
    have e3 : -((Γ).b 1 : ℚ) < (Γ).a (Γ).m := low_lt_a D C τ le_rfl
    linarith

end Min

theorem weights_top_grid : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (τ : D.what₂.Tau),
    Formalism.L2.Col.Br.Interlace G.sp.topDec.rank.symm (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) ∧
      Formalism.L2.Col.Br.SameShift (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) := by
  intro D T L sc G τ
  have r0 := rank_top G (j := D.R.m) le_rfl
  have r1 := rank_grid G (i := D.R.m) le_rfl
  have h0 := isHC_top D sc.cGap τ (j := D.R.m) le_rfl r0
  have h1 := isHC_grid D sc.cGap τ (i := D.R.m) le_rfl r1
  have hA := h0.1.card_entries.trans h0.2.1
  have hB := h1.1.card_entries.trans h1.2.1
  have eA : entries (Node.par D sc.cGap (.top D.R.m) τ) = (num D sc.cGap τ).weightX D.R.m := entries_plus _
  have eB : entries (Node.par D sc.cGap (.grid D.R.m D.R.m) τ) = entries ((num D sc.cGap τ).parD D.R.m D.R.m) := by
    have : entries (Node.par D sc.cGap (.grid D.R.m D.R.m) τ) =
        entries (shift (if Odd (D.R.m + D.R.m) then -(1 / 2) else 0) ((num D sc.cGap τ).parD D.R.m (num D sc.cGap τ).m)) := rfl
    rw [this, if_neg (by rw [Nat.odd_iff]; omega), shift_zero]
    rfl
  have hSI : StrictInterlace (entries (Node.par D sc.cGap (.top D.R.m) τ))
      (entries (Node.par D sc.cGap (.grid D.R.m D.R.m) τ)) := by
    rw [eA, eB]; exact strictInterlace_of_good (good_top_grid D sc.cGap τ)
  have hn : 0 < (G.V (.grid D.R.m D.R.m)).rank := by rw [r1]; exact rankV_pos D _ _
  refine ⟨interlace_wtOf G.sp.topDec.rank.symm hA hB h0.2.2 h1.2.2 hSI,
    sameShift_wtOf G.sp.topDec.rank.symm hn hA hB h0.2.2 h1.2.2
      (x := -((num D sc.cGap τ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2) ?_ ?_ ?_ ?_⟩
  · rw [eA]; exact low_mem_weightX D sc.cGap τ
  · rw [eA]; exact fun y hy => min_weightX D sc.cGap τ hy
  · rw [eB]; exact half_mem_parD D sc.cGap τ
  · rw [eB]; exact fun y hy => min_parD D sc.cGap τ hy

end GlobalTheory.WtInterlaceC
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def OpenBdd {a : Type} [Fintype a] [DecidableEq a] (H : Subgroup (GL a k)) : Prop :=
  IsOpen (H : Set (GL a k)) ∧ ∃ C : Set (GL a k), IsCompact C ∧ (H : Set (GL a k)) ⊆ C

theorem openBdd_of_le {a : Type} [Fintype a] [DecidableEq a] {H : Subgroup (GL a k)} (h1 : KOne k a ≤ H) (h2 : H ≤ KO k a) :
    OpenBdd H :=
  ⟨Subgroup.isOpen_mono h1 isOpen_KOne, _, isCompact_KO, h2⟩

theorem OpenBdd.map {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {H : Subgroup (GL a k)}
    (hH : OpenBdd H) (f : GL a k ≃* GL b k) (hf : Continuous f) (hf' : Continuous f.symm) : OpenBdd (H.map f.toMonoidHom) := by
  have e : ((H.map f.toMonoidHom : Subgroup (GL b k)) : Set (GL b k)) = f.symm ⁻¹' (H : Set (GL a k)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_map, Set.mem_preimage, MulEquiv.coe_toMonoidHom]
    exact ⟨fun ⟨y, hy, e⟩ => by rw [← e, MulEquiv.symm_apply_apply]; exact hy,
      fun h => ⟨_, h, MulEquiv.apply_symm_apply _ _⟩⟩
  obtain ⟨ho, C, hC, hHC⟩ := hH
  refine ⟨e ▸ ho.preimage hf', f '' C, hC.image hf, ?_⟩
  rw [e]
  intro x hx
  exact ⟨_, hHC hx, MulEquiv.apply_symm_apply _ _⟩

theorem continuous_reGL {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    Continuous (reGL (k := k) e) :=
  Continuous.units_map _ (continuous_id.matrix_reindex _ _)

theorem continuous_reGL_symm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    Continuous (reGL (k := k) e).symm := by
  have : (reGL (k := k) e).symm = reGL e.symm := by
    ext g i j
    rfl
  rw [this]
  exact continuous_reGL e.symm

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem openBdd_givenLevel (t : T) (w : Pl D.host.E) (i : ℕ) : OpenBdd (givenLevel G t w (i, D.R.m)) := by
  obtain ⟨m', hm⟩ : ∃ m', D.R.m = m' + 1 := ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩
  have key : ∀ X : ℕ × ℕ, X = (i, m' + 1) → OpenBdd (givenLevel G t w X) := by
    rintro _ rfl
    rcases i with _ | i
    · refine OpenBdd.map ?_ _ (continuous_reGL _) (continuous_reGL_symm _)
      unfold stepGroup
      split_ifs
      · exact openBdd_of_le (TypeDatum.KOne_le _) (TypeDatum.le_KO _)
      · exact openBdd_of_le (TypeDatum.KOne_le _) (TypeDatum.le_KO _)
      · exact openBdd_of_le KOne_le_KO le_rfl
    · exact openBdd_of_le KOne_le_KO le_rfl
  exact key _ (by rw [hm])

theorem openBdd_conjLevel (t : T) (w : Pl D.host.E) (g : (locGrid G t w).VertexGroup) {j : ℕ} (h0 : 0 < j)
    (hj : j < (locGrid G t w).m) : OpenBdd (conjLevel (G := locGrid G t w) one_le_sLen (givenLevel G t w) g hj) := by
  have hK : OpenBdd (givenLevel G t w ((locGrid G t w).m, j)) := by
    obtain ⟨m', hm⟩ : ∃ m', (locGrid G t w).m = m' + 1 := ⟨(locGrid G t w).m - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have key : ∀ X : ℕ × ℕ, X = (m' + 1, j' + 1) → OpenBdd (givenLevel G t w X) := by
      rintro _ rfl
      exact openBdd_of_le KOne_le_KO le_rfl
    exact key _ (by rw [hm])
  refine OpenBdd.map (OpenBdd.map hK _ ?_ ?_) _ ?_ ?_
  · exact (continuous_const.mul continuous_id).mul continuous_const
  · exact (continuous_const.mul continuous_id).mul continuous_const
  · exact Continuous.units_map _ (continuous_id.matrix_reindex _ _)
  · exact Continuous.units_map _ (continuous_id.matrix_reindex _ _)

theorem isCO_prodLev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ}
    (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (hK : ∀ w, OpenBdd (K w)) :
    IsCO V (prodLev β P h K) :=
  have ho := ProdOpen.isOpen_comap_prodLev V β P h K fun w => (hK w).1
  ⟨ho, GlobalTheory.ProdLevCompactC.isCompact_levA V β P h K (fun w => (hK w).2) ho⟩

variable (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)

theorem openBdd_pr (β : CosFam G t) (w : locPl G t) (j : ℕ) (h0 : 0 < j) (hj : j < D.R.m) :
    OpenBdd ((S.term t Φ β w).pr j h0 hj) := by
  obtain ⟨ho, hb⟩ := openBdd_conjLevel t w.1 ((repsAt G t w).elt (β w)) h0 hj
  exact SymImageC.symPr_open_bounded _ ho hb

namespace GridChoice

theorem isCO_levTop (β : CosFam G t) {j : ℕ} (hj : j < D.R.m) : IsCO (G.V (.top j)) (S.levTop t Φ β j hj) := by
  rcases j with _ | j
  · exact congLev_open_compact _ (isV_Xp G).sd.1 (G.pl.modul_ne_bot sc)
  · exact isCO_prodLev _ _ _ _ _ fun w => openBdd_pr W S t Φ β w (j + 1) j.succ_pos hj

theorem isCO_levRow {i : ℕ} (hi : i ≤ D.R.m) : IsCO (G.V (.grid i D.R.m)) (S.levRow t i hi) :=
  isCO_prodLev _ _ _ _ _ fun w => openBdd_givenLevel t w.1 i

end GridChoice

variable (G) in

theorem posDef_top {j : ℕ} (hj : j ≤ D.R.m) (φ : D.host.E →+* ℂ) : ((G.V (.top j)).gram.map φ).PosDef := by
  have h := G.isV (X := .top j) hj (fun _ e => by cases e)
  have := h.sigOK φ
  rw [h.sig φ] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem posDef_grid {μ₀ : T} (hL : L.Is μ₀) {i : ℕ} (hi : i ≤ D.R.m) (φ : D.host.E →+* ℂ) :
    ((G.V (.grid i D.R.m)).gram.map φ).PosDef := by
  have h := node_isV G hL (X := .grid i D.R.m) ⟨hi, le_rfl⟩
  have := h.sigOK φ
  rw [h.sig φ] at this
  simp only [Node.neg, Nat.sub_self, Nat.zero_div, Nat.sub_zero] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem readOK {n : ℕ} (σ : D.what₂.Tau → DomWeight n) : ReadOK σ := by
  obtain ⟨φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ φ fun F => (h F _).2 rfl

namespace GridChoice

theorem sumOK_classes {μ₀ : T} (hL : L.Is μ₀) :
    (∀ β, Finite (S.Classes t Φ β)) ∧ (∀ β (c : S.Classes t Φ β), S.invGam c ≠ 0) ∧
    (∀ i, i < D.R.m → WtOK G (.top t i) ∧ WtOK G (.chi i D.R.m)) ∧
    (∀ τ, Formalism.L2.Col.Br.Interlace G.sp.topDec.rank.symm (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) ∧
      Formalism.L2.Col.Br.SameShift (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ)) ∧
    (ReadOK (listedWt G (.grid 0 D.R.m)) ∧ ReadOK (listedWt G (.grid D.R.m D.R.m))) := by
  have hT : ∀ β (j : Fin D.R.m), Finite (FinCl _ (S.levTop t Φ β j j.2)) ∧ ∀ x, gamOrd _ (S.levTop t Φ β j j.2) x ≠ 0 :=
    fun β j => ClassFin.finite_finCl_and_gamOrd _ _ (posDef_top G j.2.le) (isCO_levTop W S t Φ β j.2)
  have hR : ∀ i : Fin (D.R.m + 1), Finite (FinCl _ (S.levRow t i (Nat.le_of_lt_succ i.2))) ∧
      ∀ x, gamOrd _ (S.levRow t i (Nat.le_of_lt_succ i.2)) x ≠ 0 :=
    fun i => ClassFin.finite_finCl_and_gamOrd _ _ (posDef_grid hL (Nat.le_of_lt_succ i.2)) (isCO_levRow W S t (Nat.le_of_lt_succ i.2))
  refine ⟨fun β => ?_, fun β c => ?_, fun i hi => ⟨wtOK_of_defPair G (.top t i) hi, wtOK_of_defPair G (.chi i D.R.m) ⟨hi, rfl⟩⟩,
    GlobalTheory.WtInterlaceC.weights_top_grid G, readOK _, readOK _⟩
  · have := fun j => (hT β j).1
    have := fun i => (hR i).1
    exact inferInstance
  · unfold GridChoice.invGam
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => inv_ne_zero (Nat.cast_ne_zero.2 ((hT β j).2 _)))
      (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (Nat.cast_ne_zero.2 ((hR i).2 _)))

end GridChoice

end GlobalTheory.FunObj

end
end
