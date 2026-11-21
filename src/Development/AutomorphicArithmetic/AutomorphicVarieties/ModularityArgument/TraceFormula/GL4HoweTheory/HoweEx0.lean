import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweChar
import Formalism.PadicSubsetSums.StableGradedCounts.BaseChangeIwahoriFactorization

section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.idemOp :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure →
      ∀ (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ χ : G → ℂ, IsLocallyConstant χ → (∀ x, ‖χ x‖ = 1) →
      (∀ x ∈ J, ∀ y ∈ J, χ (x * y) = χ x * χ y) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
        ∃ (B : V →ₗ[ℂ] V) (m : ℂ), m ≠ 0 ∧ IsIntegralOp μ π ((J : Set G).indicator fun x => (χ x)⁻¹) B ∧
          (∀ v, ∀ x ∈ J, π x (B v) = χ x • B v) ∧ ∀ v, (∀ x ∈ J, π x v = χ x • v) → B v = m • v := by
  intro G _ _ _ _ _ _ μ hμ J hJo hJc χ hχ hn hm V _ _ π hπ
  classical
  set f : G → ℂ := (J : Set G).indicator fun x => (χ x)⁻¹ with hfdef
  have hne : ∀ x, χ x ≠ 0 := fun x h => by simpa [h] using hn x
  have hJcl : IsClopen (J : Set G) := ⟨hJc.isClosed, hJo⟩
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h1 := (IsLocallyConstant.iff_eventually_eq χ).1 hχ x
    by_cases hx : x ∈ (J : Set G)
    · filter_upwards [h1, hJo.mem_nhds hx] with y hy hyJ
      simp only [hfdef, Set.indicator_of_mem hx, Set.indicator_of_mem hyJ, hy]
    · filter_upwards [hJcl.isClosed.isOpen_compl.mem_nhds hx] with y hyJ
      simp only [hfdef, Set.indicator_of_notMem hx, Set.indicator_of_notMem hyJ]
  have hc : HasCompactSupport f :=
    HasCompactSupport.intro hJc fun x hx => Set.indicator_of_notMem hx _
  have hB : IsIntegralOp μ π f (GlobalTheory.OpTrace.smoothOp π μ f) := by
    intro v l
    have hi := hπ.smoothOp_integrand hf hc v
    refine ⟨?_, ?_⟩
    · have := GlobalTheory.OpTrace.integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
      simpa only [map_smul, smul_eq_mul] using this
    · rw [hπ.map_smoothOp (μ := μ) hf hc l v]
      simp only [smul_eq_mul]
  generalize GlobalTheory.OpTrace.smoothOp π μ f = B at hB
  refine ⟨B, (μ.real (J : Set G) : ℂ), ?_, hB, ?_, ?_⟩
  · have h0 : μ (J : Set G) ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
    have h1 : μ (J : Set G) ≠ ⊤ := hJc.measure_lt_top.ne
    have : μ.real (J : Set G) ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨h0, h1⟩
    exact_mod_cast this
  · intro v x hx
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    have h1 := (hB v (l ∘ₗ π x)).2
    have h2 := (hB v l).2
    rw [map_sub, map_smul, sub_eq_zero, h2, smul_eq_mul, ← integral_const_mul,
      ← integral_mul_left_eq_self (fun g => χ x * (f g * l (π g v))) x]
    refine h1.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))
    have e : χ x * f (x * g) = f g := by
      by_cases hg : g ∈ J
      · have hxg : x * g ∈ (J : Set G) := J.mul_mem hx hg
        have hg' : g ∈ (J : Set G) := hg
        simp only [hfdef, Set.indicator_of_mem hxg, Set.indicator_of_mem hg', hm x hx g hg]
        have := hne x
        have := hne g
        field_simp
      · have hxg : x * g ∉ (J : Set G) := fun h => hg ((J.mul_mem_cancel_left hx).1 h)
        have hg' : g ∉ (J : Set G) := hg
        simp only [hfdef, Set.indicator_of_notMem hxg, Set.indicator_of_notMem hg', mul_zero]
    simp only [← mul_assoc, e, map_mul, LinearMap.comp_apply, Module.End.mul_apply]
  · intro v hv
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, map_smul, sub_eq_zero, (hB v l).2]
    have e : (fun g => f g * l (π g v)) = (J : Set G).indicator fun _ => l v := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · simp only [hfdef, Set.indicator_of_mem hg, hv g hg, map_smul, smul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (hne g), one_mul]
      · simp only [hfdef, Set.indicator_of_notMem hg, zero_mul]
    rw [e, integral_indicator_const _ hJo.measurableSet]
    simp
end

section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.ulFact :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a → ∀ x ∈ howeSet n ϖ a c,
      ∃ u ∈ unipB E (Fin n), ∃ b ∈ howeSet n ϖ a c, x = u * b ∧ ∀ i j : Fin n, i < j → (b : Matrix (Fin n) (Fin n) E) i j = 0 := by
  intro E _ _ _ _ n ϖ hϖ a c ha x hx
  have hlt : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    exact zpow_lt_one₀ (by rw [← hϖ]; exact (Valuation.pos_iff _).2 ϖ.ne_zero) uniformizer_lt_one (by omega)
  let t : Fin n → Eˣ := fun i => ϖ ^ (c * ((i : ℕ) : ℤ))
  let w : Fin n → Fin n → E := fun i j => ((t i * (t j)⁻¹ : Eˣ) : E)
  have hw0 : ∀ i j, w i j ≠ 0 := fun i j => Units.ne_zero _
  have hwi : ∀ i, w i i = 1 := fun i => by simp [w]
  have hww : ∀ i k j, w i k * w k j = w i j := fun i k j => by
    simp only [w]
    rw [← Units.val_mul]
    congr 1
    group
  have hpow : ∀ i j : Fin n, ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) = ((ϖ ^ a : Eˣ) : E) * w i j := fun i j => by
    simp only [w, t]
    rw [← Units.val_mul, ← zpow_neg, ← zpow_add, ← zpow_add]
    congr 2
    ring
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) E) i j * w i j = (1 : Matrix (Fin n) (Fin n) E) i j := fun i j => by
    by_cases h : i = j
    · subst h; rw [hwi, mul_one]
    · rw [Matrix.one_apply_ne h, zero_mul]
  have key : ∀ (i j : Fin n) (z : E), valuation E (z * w i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤
      valuation E ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) ↔
      valuation E (z - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ valuation E ((ϖ ^ a : Eˣ) : E) := fun i j z => by
    rw [hpow, ← hone i j, ← sub_mul, hone, map_mul, map_mul]
    exact mul_le_mul_iff_left₀ ((Valuation.pos_iff (valuation E)).2 (hw0 i j))
  have hg : ∀ i j, valuation E ((x : Matrix (Fin n) (Fin n) E) i j / w i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤
      valuation E ((ϖ ^ a : Eˣ) : E) := fun i j => (key i j _).1 (by rw [div_mul_cancel₀ _ (hw0 i j)]; exact hx i j)
  have h1 : ∀ i j, valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := fun i j => by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hint : ∀ i j, (x : Matrix (Fin n) (Fin n) E) i j / w i j ∈ 𝒪[E] := fun i j => by
    change valuation E _ ≤ 1
    rw [← sub_add_cancel (_ / w i j) ((1 : Matrix (Fin n) (Fin n) E) i j)]
    exact Valuation.map_add_le _ ((hg i j).trans hlt.le) (h1 i j)
  let I : Ideal 𝒪[E] :=
    { carrier := {z | valuation E (z : E) ≤ valuation E ((ϖ ^ a : Eˣ) : E)}
      add_mem' := fun {y z} h h' => by
        rw [Set.mem_setOf_eq] at h h' ⊢
        rw [Subring.coe_add]
        exact Valuation.map_add_le _ h h'
      zero_mem' := by simp
      smul_mem' := fun r z h => by
        rw [Set.mem_setOf_eq] at h ⊢
        rw [smul_eq_mul, Subring.coe_mul, map_mul]
        simpa using mul_le_mul' (show valuation E (r : E) ≤ 1 from r.2) h }
  have hI : ∀ z : 𝒪[E], z ∈ I ↔ valuation E (z : E) ≤ valuation E ((ϖ ^ a : Eˣ) : E) := fun _ => Iff.rfl
  have hIm : I ≤ IsLocalRing.maximalIdeal 𝒪[E] := IsLocalRing.le_maximalIdeal fun h => by
    have : (1 : 𝒪[E]) ∈ I := h ▸ Submodule.mem_top
    rw [hI] at this
    exact absurd (lt_of_le_of_lt this hlt) (by simp)
  let g : Matrix (Fin n) (Fin n) 𝒪[E] := fun i j => ⟨_, hint i j⟩
  have hgd : ∀ i, g i i - 1 ∈ I := fun i => by
    have := hg i i
    rwa [Matrix.one_apply_eq] at this
  have hgo : ∀ i j, i ≠ j → g i j ∈ I := fun i j h => by
    have := hg i j
    rwa [Matrix.one_apply_ne h, sub_zero] at this
  obtain ⟨X, Y, δ, e, x1, x0, -, -, hδ, y1, y0, yL⟩ := Formalism.IrreducibleCountingLemmas.Z.iwahori_factorization_exists 𝒪[E] I I hIm n g
    (fun i => by
      have := Formalism.IrreducibleCountingLemmas.Z.isUnit_sub_of_mem_maximalIdeal isUnit_one (hIm (I.neg_mem (hgd i)))
      simpa using this)
    (fun i j h => hgo i j h.ne) fun i j h => hgo i j h.ne'
  let U : Matrix (Fin n) (Fin n) E := fun i j => (X i j : E) * w i j
  let B : Matrix (Fin n) (Fin n) E := fun i j => ((δ i * Y i j : 𝒪[E]) : E) * w i j
  have hU0 : ∀ i j, j < i → U i j = 0 := fun i j h => by simp [U, x0 i j h]
  have hU1 : ∀ i, U i i = 1 := fun i => by simp [U, x1, hwi]
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hU0 i j h)]
    simp [hU1]
  let u : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero U hdet
  have hUB : U * B = (x : Matrix (Fin n) (Fin n) E) := by
    ext i j
    have h2 : (x : Matrix (Fin n) (Fin n) E) i j / w i j = ∑ k, (X i k : E) * δ k * Y k j := by
      have := congrArg (fun z : 𝒪[E] => (z : E)) (e i j)
      simpa [g] using this
    rw [← div_mul_cancel₀ ((x : Matrix (Fin n) (Fin n) E) i j) (hw0 i j), h2, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [U, B]
    rw [← hww i k j]
    push_cast
    ring
  have hb : ((u⁻¹ * x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = B := by
    rw [Units.val_mul, ← hUB]
    change (u⁻¹).val * (u.val * B) = B
    rw [← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨u, (mem_unipB E).2 ⟨hU0, hU1⟩, u⁻¹ * x, fun i j => ?_, (mul_inv_cancel_left _ _).symm, fun i j h => ?_⟩
  · rw [hb]
    refine (key i j _).2 ?_
    rcases lt_trichotomy i j with h | h | h
    · rw [y0 i j h, Matrix.one_apply_ne h.ne]
      simp
    · subst h
      rw [y1, mul_one, Matrix.one_apply_eq]
      have : δ i - 1 ∈ I := by
        simpa using I.add_mem (Ideal.mul_le_left (hδ i)) (hgd i)
      exact this
    · rw [Matrix.one_apply_ne h.ne', sub_zero]
      exact (hI _).1 (I.mul_mem_left _ (yL i j h))
  · rw [hb]
    simp [B, y0 i j h]
end

section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

open Topology Filter in
private theorem lowFix_emb (E : Type) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E] (n : ℕ) :
    IsEmbedding (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Matrix (Fin n) (Fin n) E => A⁻¹) ?_ ?_
  · intro A hA
    refine (continuousAt_matrix_inv A ?_).continuousWithinAt
    have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  · intro u
    exact (Matrix.coe_units_inv u).symm

open Topology Filter in
private theorem lowFix_ball (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (γ : ValueGroupWithZero E) (hγ : γ < 1) (W : Set E) (hW : W ∈ nhds (0 : E)) :
    ∃ m : ℕ, ∀ x : E, valuation E x ≤ γ ^ m → x ∈ W := by
  obtain ⟨δ, hδ⟩ := (IsValuativeTopology.mem_nhds_zero_iff W).1 hW
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hγ δ
  exact ⟨m, fun x hx => hδ (lt_of_le_of_lt hx hm)⟩

open Topology Filter in
theorem UpperTheory.V.Z.Tf.L4.lowFix :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (d : ℤ) (U : Set (GL (Fin n) E)), U ∈ nhds (1 : GL (Fin n) E) →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, ∀ b ∈ howeSet n ϖ a (2 * a - d), (∀ i j : Fin n, i < j → (b : Matrix (Fin n) (Fin n) E) i j = 0) → b ∈ U := by
  intro E _ _ _ _ n ϖ hϖ d U hU
  have hlt : valuation E (ϖ : E) < 1 := hϖ ▸ uniformizer_lt_one
  have hpos : 0 < valuation E (ϖ : E) := zero_lt_iff.2 (by simp)
  rw [(lowFix_emb E n).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  have hc : Continuous (fun A : Fin n → Fin n → E => (Matrix.of A + 1 : Matrix (Fin n) (Fin n) E)) :=
    Continuous.add (f := fun A : Fin n → Fin n → E => (Matrix.of A : Matrix (Fin n) (Fin n) E)) continuous_id continuous_const
  have h0 : (fun A : Fin n → Fin n → E => (Matrix.of A + 1 : Matrix (Fin n) (Fin n) E)) ⁻¹' T ∈ nhds (0 : Fin n → Fin n → E) := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hT
  have key : ∃ m : ℕ, ∀ A : Fin n → Fin n → E, (∀ i j, valuation E (A i j) ≤ valuation E (ϖ : E) ^ m) →
      Matrix.of A + 1 ∈ T := by
    rw [nhds_pi, Filter.mem_pi'] at h0
    obtain ⟨I, t, ht, htI⟩ := h0
    have h1 : ∀ i, ∃ s : Fin n → Set E, (∀ j, s j ∈ nhds (0 : E)) ∧ Set.pi Set.univ s ⊆ t i := by
      intro i
      have := ht i
      rw [nhds_pi, Filter.mem_pi'] at this
      obtain ⟨J, s, hs, hsJ⟩ := this
      exact ⟨s, hs, fun x hx => hsJ fun j _ => hx j (Set.mem_univ _)⟩
    choose s hs hst using h1
    have hW : (⋂ i, ⋂ j, s i j) ∈ nhds (0 : E) :=
      Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => hs i j
    obtain ⟨m, hm⟩ := lowFix_ball E _ hlt _ hW
    refine ⟨m, fun A hA => htI fun i _ => hst i fun j _ => ?_⟩
    have := hm _ (hA i j)
    simp only [Set.mem_iInter] at this
    exact this i j
  obtain ⟨m, hm⟩ := key
  refine ⟨max (m : ℤ) |d|, fun a ha b hb hlow => hTU ?_⟩
  have ham : (m : ℤ) ≤ a := le_trans (le_max_left _ _) ha
  have had : |d| ≤ a := le_trans (le_max_right _ _) ha
  have hc0 : 0 ≤ 2 * a - d := by
    have := le_abs_self d
    have := abs_nonneg d
    omega
  have := hm (fun i j => (b : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) (by
    intro i j
    rcases lt_or_ge i j with hij | hij
    · simp [hlow i j hij, Matrix.one_apply_ne hij.ne]
    · refine le_trans (hb i j) ?_
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_natCast]
      refine zpow_le_zpow_right_of_le_one₀ hpos hlt.le ?_
      have hji : ((j : ℕ) : ℤ) ≤ ((i : ℕ) : ℤ) := by exact_mod_cast hij
      have := mul_nonneg hc0 (sub_nonneg.2 hji)
      omega)
  have e : (Matrix.of (fun i j => (b : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) + 1 : Matrix (Fin n) (Fin n) E) = (b : Matrix (Fin n) (Fin n) E) := by
    ext i j
    simp
  rw [e] at this
  exact this
end

section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.howeEx0 :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π →
      ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ (ψ : AddChar E Circle) (d : ℤ), HasConductor ψ (ϖ ^ d) → GlobalTheory.LocGL.IsGenericFor ψ π →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, howeSpace π ψ (howeSet n ϖ a (2 * a - d)) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ ψ d hψ hg
  obtain ⟨l, v, hlv, hl⟩ : ∃ (l : Module.Dual ℂ V) (v : V), l v ≠ 0 ∧
      ∀ u ∈ unipB E (Fin n), ∀ x, l (π u x) = (ψ (GlobalTheory.Whittaker.superDiag u) : ℂ) * l x := by
    haveI : Nontrivial (TwJacquet π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n)) := hg
    obtain ⟨w, hw⟩ := exists_ne (0 : TwJacquet π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n))
    obtain ⟨l₀, h₀⟩ := Module.Projective.exists_dual_ne_zero ℂ hw
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨l₀ ∘ₗ Submodule.mkQ _, v, h₀, fun u hu x => ?_⟩
    have h1 : π u x - (GlobalTheory.LocGL.whitChar ψ n ⟨u, hu⟩ : ℂ) • x ∈ twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n) :=
      Submodule.subset_span ⟨⟨u, hu⟩, x, rfl⟩
    have h2 : (GlobalTheory.LocGL.whitChar ψ n ⟨u, hu⟩ : ℂ) = (ψ (GlobalTheory.Whittaker.superDiag u) : ℂ) := by
      have : (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) = GlobalTheory.Whittaker.superDiag u := by
        rw [GlobalTheory.Whittaker.superDiag, Finset.sum_filter, Fintype.sum_prod_type]
        simp only [Finset.sum_filter]
      rw [← this]
      rfl
    have h3 := (Submodule.Quotient.eq _).2 h1
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [h3, h2, Submodule.Quotient.mk_smul, map_smul, smul_eq_mul]
  obtain ⟨a₀, h₀⟩ := UpperTheory.V.Z.Tf.L4.lowFix E n ϖ hϖ d {g | π g v = v} ((hs v).mem_nhds (by simp))
  refine ⟨max 1 a₀, fun a ha => ?_⟩
  have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
  have hψ' : HasConductor ψ (ϖ ^ (2 * a - (2 * a - d))) := by rwa [sub_sub_cancel]
  obtain ⟨J, hJ, ho, hk⟩ := UpperTheory.V.Z.Tf.L4.howeGroup E n ϖ hϖ a (2 * a - d) ha1
  obtain ⟨hlc, hmul⟩ := UpperTheory.V.Z.Tf.L4.howeChar E n ϖ hϖ a (2 * a - d) ha1 ψ hψ'
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a (2 * a - d) := fun x => by rw [← hJ]; rfl
  haveI : LocallyCompactSpace (GL (Fin n) E) := hk.locallyCompactSpace_of_mem_nhds_of_group (ho.mem_nhds J.one_mem)
  borelize (GL (Fin n) E)
  let μ : Measure (GL (Fin n) E) := Measure.haar
  obtain ⟨B, m, -, hB, hB1, -⟩ := UpperTheory.V.Z.Tf.L4.idemOp (GL (Fin n) E) μ inferInstance J ho hk _ hlc (fun x => Circle.norm_coe _)
    (fun x hx y hy => by rw [hmul x ((hmem x).1 hx) y ((hmem y).1 hy), Circle.coe_mul]) V π hs
  refine (Submodule.ne_bot_iff _).2 ⟨B v, fun x hx => hB1 v x ((hmem x).2 hx), fun h => ?_⟩
  have h1 := (hB v l).2
  have e : (fun g => (J : Set (GL (Fin n) E)).indicator (fun x => ((ψ (GlobalTheory.Whittaker.superDiag x) : ℂ))⁻¹) g * l (π g v)) =
      (J : Set (GL (Fin n) E)).indicator fun _ => l v := by
    funext g
    by_cases hgJ : g ∈ (J : Set (GL (Fin n) E))
    · rw [Set.indicator_of_mem hgJ, Set.indicator_of_mem hgJ]
      obtain ⟨u, hu, b, hb, hub, hlow⟩ := UpperTheory.V.Z.Tf.L4.ulFact E n ϖ hϖ a (2 * a - d) ha1 g ((hmem g).1 hgJ)
      have hbv : π b v = v := h₀ a (le_trans (le_max_right _ _) ha) b hb hlow
      have huJ : u ∈ J := by
        have : u = g * b⁻¹ := by rw [hub, mul_inv_cancel_right]
        rw [this]
        exact J.mul_mem hgJ (J.inv_mem ((hmem b).2 hb))
      have hsd : GlobalTheory.Whittaker.superDiag b = 0 :=
        Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => hlow i j (by
          have := (Finset.mem_filter.1 hj).2
          rw [Fin.lt_def]
          omega)
      rw [hub, hmul u ((hmem u).1 huJ) b hb, hsd, AddChar.map_zero_eq_one, mul_one, map_mul, Module.End.mul_apply, hbv,
        hl u hu, ← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
    · rw [Set.indicator_of_notMem hgJ, Set.indicator_of_notMem hgJ, zero_mul]
  rw [e, h, map_zero, integral_indicator_const _ ho.measurableSet] at h1
  rcases smul_eq_zero.1 h1.symm with h2 | h2
  · exact ((ENNReal.toReal_pos (ho.measure_ne_zero μ ⟨1, J.one_mem⟩) hk.measure_lt_top.ne).ne') h2
  · exact hlv h2
end
