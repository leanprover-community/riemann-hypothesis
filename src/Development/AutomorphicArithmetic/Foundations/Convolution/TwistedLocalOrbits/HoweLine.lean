import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.InjMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweChar
import Development.DiscreteGroups.GlobalIrreducibility.DzGenCpt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.CondEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.CharDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweEx0
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric

section
open GlobalTheory.PRep MeasureTheory

namespace UpperTheory.ConvolutionTheory.Loc

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

private theorem cont_coeff {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (l : V →ₗ[ℂ] ℂ) (w : V) :
    Continuous fun g : G => l (ρ g w) := by
  have h : IsLocallyConstant fun g : G => ρ g w := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun g => x⁻¹ * g) ⁻¹' {g | ρ g w = w}, (hρ w).preimage (continuous_const.mul continuous_id), by simp, ?_⟩
    intro y hy
    have hy' : ρ (x⁻¹ * y) w = w := hy
    calc ρ y w = ρ x (ρ (x⁻¹ * y) w) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ x w := by rw [hy']
  exact (h.comp l).continuous

open Classical in
private theorem avg {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (C : Subgroup G) (hC : IsCompact (C : Set G))
    (θ : G → ℂ) (hθ : Continuous θ) (hmul : ∀ a ∈ C, ∀ b ∈ C, θ (a * b) = θ a * θ b) (l : V →ₗ[ℂ] ℂ) (v : V)
    (S : Set G) (hS : IsOpen S) (h1 : 1 ∈ S) (hv : ∀ c ∈ C, θ c * l (ρ c⁻¹ v) = if c ∈ S then 1 else 0) :
    ∃ l' : V →ₗ[ℂ] ℂ, (∀ c ∈ C, ∀ w, l' (ρ c w) = θ c * l' w) ∧ l' v = 1 := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
  letI : MeasurableSpace C := borel C
  haveI : BorelSpace C := ⟨rfl⟩
  let μ : Measure C := Measure.haar
  have hc : ∀ w, Continuous fun c : C => θ c * l (ρ (c : G)⁻¹ w) := fun w =>
    (hθ.comp continuous_subtype_val).mul ((cont_coeff hρ l w).comp continuous_subtype_val.inv)
  have hi : ∀ w, Integrable (fun c : C => θ c * l (ρ (c : G)⁻¹ w)) μ := fun w =>
    (hc w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L : V →ₗ[ℂ] ℂ :=
    { toFun := fun w => ∫ c : C, θ c * l (ρ (c : G)⁻¹ w) ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hi a) (hi b)]
        simp only [map_add, mul_add]
      map_smul' := fun t a => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext c
        ring }
  have hL : ∀ c ∈ C, ∀ w, L (ρ c w) = θ c * L w := by
    intro c hc w
    change ∫ x : C, θ x * l (ρ (x : G)⁻¹ (ρ c w)) ∂μ = θ c * ∫ x : C, θ x * l (ρ (x : G)⁻¹ w) ∂μ
    rw [← integral_const_mul, ← integral_mul_left_eq_self _ (⟨c, hc⟩ : C)]
    congr 1
    funext x
    simp only [Subgroup.coe_mul]
    rw [hmul c hc x x.2, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right, mul_assoc]
  have hT : IsOpen ((Subtype.val : C → G) ⁻¹' S) := hS.preimage continuous_subtype_val
  have hLv : L v = (μ.real ((Subtype.val : C → G) ⁻¹' S) : ℂ) := by
    change ∫ x : C, θ x * l (ρ (x : G)⁻¹ v) ∂μ = _
    have : (fun x : C => θ x * l (ρ (x : G)⁻¹ v)) = ((Subtype.val : C → G) ⁻¹' S).indicator fun _ => (1 : ℂ) := by
      funext x
      rw [hv x x.2, Set.indicator_apply]
      rfl
    rw [this, integral_indicator_const _ hT.measurableSet]
    simp
  have hne : L v ≠ 0 := by
    rw [hLv, Complex.ofReal_ne_zero, measureReal_ne_zero_iff (measure_ne_top _ _)]
    exact hT.measure_ne_zero μ ⟨1, h1⟩
  refine ⟨(L v)⁻¹ • L, fun c hc w => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, hL c hc, smul_eq_mul]
    ring
  · simp [hne]

theorem eq_zero_of_no_intertwining {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (K N : Subgroup G)
    (hK : IsCompact (K : Set G)) (hK' : IsOpen (K : Set G))
    (hN : ∀ F : Finset G, (∀ u ∈ F, u ∈ N) → ∃ C : Subgroup G, IsCompact (C : Set G) ∧ C ≤ N ∧ ∀ u ∈ F, u ∈ C)
    (χ : G → ℂ) (hχ : Continuous χ) (hmul : ∀ a ∈ N, ∀ b ∈ N, χ (a * b) = χ a * χ b)
    (hint : ∀ u ∈ N, u ∉ K → ∃ k ∈ K, u * k * u⁻¹ ∈ K ∧ χ (u * k * u⁻¹) ≠ χ k)
    (v : V) (hv : ∀ k ∈ K, ρ k v = χ k • v)
    (hker : v ∈ Submodule.span ℂ {w | ∃ u ∈ N, ∃ x, w = ρ u x - χ u • x}) : v = 0 := by
  classical
  by_contra h0
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  have hK1 : ∀ k ∈ K, χ k = l₀ (ρ k v) := fun k hk => by rw [hv k hk, map_smul, hl₀, smul_eq_mul, mul_one]
  have hKmul : ∀ a ∈ K, ∀ b ∈ K, χ (a * b) = χ a * χ b := fun a ha b hb => by
    rw [hK1 _ (K.mul_mem ha hb), map_mul, Module.End.mul_apply, hv b hb, map_smul, map_smul, ← hK1 a ha, smul_eq_mul,
      mul_comm]
  have hinv : ∀ a ∈ K, χ a * χ a⁻¹ = 1 := fun a ha => by
    rw [← hKmul a ha _ (K.inv_mem ha), mul_inv_cancel, hK1 1 K.one_mem, map_one, Module.End.one_apply, hl₀]
  obtain ⟨l₁, hl₁, hl₁v⟩ := avg hρ K hK χ hχ hKmul l₀ v Set.univ isOpen_univ trivial (fun c hc => by
    rw [← hK1 _ (K.inv_mem hc), hinv c hc]; simp)
  have hF : ∃ F : Finset G, (∀ u ∈ F, u ∈ N) ∧
      ∀ l' : V →ₗ[ℂ] ℂ, (∀ c ∈ F, ∀ w, l' (ρ c w) = χ c * l' w) → l' v = 0 := by
    clear hl₁v hv hK1 hl₀ h0
    induction hker using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨u, hu, x, rfl⟩ := hw
      exact ⟨{u}, by simpa using hu, fun l' h => by simp [h u (by simp)]⟩
    | zero => exact ⟨∅, by simp, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨F, hF, h⟩ := ha
      obtain ⟨F', hF', h'⟩ := hb
      refine ⟨F ∪ F', fun u hu => (Finset.mem_union.1 hu).elim (hF u) (hF' u), fun l' hl => ?_⟩
      rw [map_add, h l' fun c hc => hl c (Finset.mem_union_left _ hc), h' l' fun c hc => hl c (Finset.mem_union_right _ hc),
        add_zero]
    | smul t a _ ha =>
      obtain ⟨F, hF, h⟩ := ha
      exact ⟨F, hF, fun l' hl => by rw [map_smul, h l' hl, smul_zero]⟩
  obtain ⟨F, hFN, hF⟩ := hF
  obtain ⟨C, hC, hCN, hFC⟩ := hN F hFN
  obtain ⟨l₂, hl₂, hl₂v⟩ := avg hρ C hC χ hχ (fun a ha b hb => hmul a (hCN ha) b (hCN hb)) l₁ v K hK' K.one_mem
    (fun c hc => by
      by_cases hcK : c ∈ K
      · rw [if_pos (by exact hcK), hv _ (K.inv_mem hcK), map_smul, hl₁v, smul_eq_mul, mul_one, hinv c hcK]
      · rw [if_neg (by exact hcK)]
        obtain ⟨k, hk, hk', hne⟩ := hint c⁻¹ (N.inv_mem (hCN hc)) (fun h => hcK (by simpa using K.inv_mem h))
        have h1 := hl₁ _ hk' (ρ c⁻¹ v)
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hv k hk, map_smul,
          map_smul, smul_eq_mul] at h1
        rw [(mul_eq_mul_right_iff.1 h1).resolve_left hne.symm, mul_zero])
  exact one_ne_zero (hl₂v.symm.trans (hF l₂ fun c hc => hl₂ c (hFC c hc)))

end UpperTheory.ConvolutionTheory.Loc
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc UpperTheory.V.Z.Tf.L4

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem conj_sub (ϖ : Eˣ) (c : ℤ) (g : GL (Fin n) E) (i j : Fin n) :
    ((diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹ : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
      ((ϖ ^ (c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) * ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
  rw [DiscreteGroups.sglob.DzType.diag_conj_apply, mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, ← mul_sub, mul_sub ((ϖ ^ _ : Eˣ) : E)]
  congr 1
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

private theorem conj_mem (ϖ : Eˣ) (a c : ℤ) (g : GL (Fin n) E) :
    diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹ ∈ howeSet n ϖ a c ↔
      Bd (valuation E ((ϖ ^ a : Eˣ) : E)) ((g : Matrix (Fin n) (Fin n) E) - 1) := by
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [conj_sub, add_comm a, _root_.zpow_add, Units.val_mul, map_mul, map_mul, Matrix.sub_apply]
  exact mul_le_mul_iff_right₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))

private theorem conj_sd (ϖ : Eˣ) (c : ℤ) (g : GL (Fin n) E) :
    GlobalTheory.Whittaker.superDiag (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹) =
      ((ϖ ^ (-c) : Eˣ) : E) * GlobalTheory.Whittaker.superDiag g := by
  simp only [GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have h := (Finset.mem_filter.1 hj).2
  rw [DiscreteGroups.sglob.DzType.diag_conj_apply, mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, h]
  congr 3
  push_cast
  ring

private theorem whit_eq (ψ : AddChar E Circle) (u : unipB E (Fin n)) :
    ((GlobalTheory.LocGL.whitChar ψ n u : ℂˣ) : ℂ) = (ψ (GlobalTheory.Whittaker.superDiag (u : GL (Fin n) E)) : ℂ) := by
  change ((ψ _ : Circle) : ℂ) = _
  congr 2
  simp only [GlobalTheory.Whittaker.superDiag, Finset.sum_filter]
  exact Fintype.sum_prod_type _

end

theorem UpperTheory.ConvolutionTheory.Loc.howeInj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → ∀ v ∈ howeSpace π ψ (howeSet n ϖ a c),
        v ∈ twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n) → v = 0 := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ a c ha ψ hψ v hv hk
  obtain ⟨J, hJ, ho, hc⟩ := howeGroup E n ϖ hϖ a c ha
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a c := fun x => by rw [← hJ]; rfl
  refine eq_zero_of_no_intertwining hs J (unipB E (Fin n)) hc ho DiscreteGroups.sglob.DzType.exists_compact_unip
    (fun x => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ)) (howeChar E n ϖ hϖ a c ha ψ hψ).1.continuous (fun x hx y hy => ?_)
    (fun u hu hn => ?_) v (fun k h => hv k ((hmem k).1 h)) (Submodule.span_mono ?_ hk)
  · have := congrArg Units.val (map_mul (GlobalTheory.LocGL.whitChar ψ n) ⟨x, hx⟩ ⟨y, hy⟩)
    rwa [Units.val_mul, whit_eq, whit_eq, whit_eq] at this
  · obtain ⟨d, hd⟩ : ∃ d, d = diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) := ⟨_, rfl⟩
    have hu' : d⁻¹ * u * d ∈ unipB E (Fin n) := by
      have e : diagT E (Fin n) (fun i => (ϖ ^ (c * (i : ℕ)))⁻¹) = d⁻¹ := by rw [hd, ← map_inv]; rfl
      have := DiscreteGroups.sglob.DzType.diag_conj_mem_unipB (fun i => (ϖ ^ (c * (i : ℕ)))⁻¹) hu
      rwa [e, inv_inv] at this
    have hp : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
      exact zpow_lt_one₀ (zero_lt_iff.2 uniformizer_ne_zero) uniformizer_lt_one (by omega)
    obtain ⟨k, h1, h2, h3⟩ := not_intertwine (ϖ ^ a) hp (ψ.mulShift ((ϖ ^ (-c) : Eˣ) : E)) (fun x hx => by
      have h0 : 0 < valuation E ((ϖ ^ (-c) : Eˣ) : E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))
      have h4 : ¬ valuation E (((ϖ ^ (-c) : Eˣ) : E) * x) ≤ valuation E ((ϖ ^ (2 * a - c) : Eˣ) : E) := by
        rw [show 2 * a - c = -c + (a + a) by ring, _root_.zpow_add, _root_.zpow_add, Units.val_mul, Units.val_mul, map_mul, map_mul _ ((ϖ ^ (-c) : Eˣ) : E),
          mul_le_mul_iff_right₀ h0]
        exact not_le.2 hx
      rw [← hψ] at h4
      push Not at h4
      obtain ⟨y, h5, h6⟩ := h4
      refine ⟨((ϖ ^ (-c) : Eˣ) : E)⁻¹ * y, ?_, by rwa [AddChar.mulShift_apply, mul_inv_cancel_left₀ (Units.ne_zero _)]⟩
      rwa [map_mul, map_inv₀, inv_mul_le_iff₀ h0, ← map_mul]) (d⁻¹ * u * d) hu' fun h => hn (by
        have := (conj_mem ϖ a c _).2 h
        rw [← hd, show d * (d⁻¹ * u * d) * d⁻¹ = u by group] at this
        exact (hmem u).2 this)
    have e : u * (d * k * d⁻¹) * u⁻¹ = d * (d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹) * d⁻¹ := by group
    refine ⟨d * k * d⁻¹, (hmem _).2 (hd ▸ (conj_mem ϖ a c k).2 h1), ?_, fun h => h3 (Circle.ext ?_)⟩
    · rw [e]
      generalize d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹ = z at h2
      exact (hmem _).2 (hd ▸ (conj_mem ϖ a c z).2 h2)
    · rw [e] at h
      generalize d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹ = z at h
      simp only [hd, conj_sd] at h
      exact h
  · rintro w ⟨u, x, rfl⟩
    exact ⟨u, u.2, x, by rw [whit_eq]⟩
end

section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.howeEx :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → GlobalTheory.LocGL.IsGeneric π → ∀ c : ℤ, ∃ a₀ : ℤ, ∀ a ≥ a₀,
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → howeSpace π ψ (howeSet n ϖ a c) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ ⟨ψ₀, h1, h2, h3⟩ c
  obtain ⟨d, hd⟩ := UpperTheory.V.Z.Tf.L4.condEx E ϖ hϖ ψ₀ h1 h2
  obtain ⟨a₀, h⟩ := UpperTheory.V.Z.Tf.L4.howeEx0 E n V π hs ϖ hϖ ψ₀ d hd h3
  refine ⟨a₀, fun a ha ψ hψ => ?_⟩
  obtain ⟨β, hβ, e⟩ := UpperTheory.V.Z.Tf.L4.charDual E ϖ hϖ ψ₀ ψ d _ hd hψ
  refine UpperTheory.V.Z.Tf.L4.howeConj E n V π ϖ β a c _ hβ ψ₀ ψ e ?_
  rw [show c - (d - (2 * a - c)) = 2 * a - d by ring]
  exact h a ha
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.whitOne :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → π.IsIrreducible → ∀ ψ : AddChar E Circle, Continuous ψ → ψ ≠ 1 →
      Module.rank ℂ (TwJacquet π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n)) ≤ 1 := by
  intro E _ _ _ _ n V _ _ π hs hirr ψ hψc hψ1
  exact PositivityTheory.rg.gu.whit.whitLeOne E n ψ V π hs hirr hψc hψ1
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.howeLine :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → π.IsIrreducible → GlobalTheory.LocGL.IsGeneric π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ c : ℤ, ∃ a₀ : ℤ, ∀ a ≥ a₀,
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → Module.finrank ℂ (howeSpace π ψ (howeSet n ϖ a c)) = 1 := by
  intro E _ _ _ _ n V _ _ π hs hi hg ϖ hϖ c
  obtain ⟨a₀, h⟩ := howeEx E n V π hs ϖ hϖ hg c
  refine ⟨max 1 a₀, fun a ha ψ hψ => ?_⟩
  have h1 := whitOne E n V π hs hi ψ hψ.continuous hψ.ne_one
  let f := (twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n)).mkQ ∘ₗ (howeSpace π ψ (howeSet n ϖ a c)).subtype
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).2 fun v hv =>
    Subtype.ext (howeInj E n V π hs ϖ hϖ a c (le_trans (le_max_left _ _) ha) ψ hψ v.1 v.2 ((Submodule.Quotient.mk_eq_zero _).1 hv))
  have h2 : Module.rank ℂ (howeSpace π ψ (howeSet n ϖ a c)) ≤ 1 := (LinearMap.rank_le_of_injective f hf).trans h1
  have h3 := Submodule.nontrivial_iff_ne_bot.2 (h a (le_trans (le_max_right _ _) ha) ψ hψ)
  exact Module.finrank_eq_of_rank_eq (le_antisymm (by simpa using h2) (by simpa using Cardinal.one_le_iff_pos.2 rank_pos))
end
