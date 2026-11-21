import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.ResidualAutomorphyOfLinkedEnds
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPushforward
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberOfBot

section
open MulAction UpperTheory.V.Z.Sym

private structure PairSp (H G : Type) [Group G] (U : Subgroup G) : Type where
  fst : H
  snd : G ⧸ U

@[instance_reducible] private def pairAct {H G : Type} [Group H] [Group G] (j : H →* G) (U : Subgroup G) :
    MulAction H (PairSp H G U) where
  smul h p := ⟨h * p.1 * h⁻¹, j h • p.2⟩
  one_smul p := by
    show (⟨(1 : H) * p.1 * (1 : H)⁻¹, j 1 • p.2⟩ : PairSp H G U) = p
    simp
  mul_smul a b p := by
    show (⟨a * b * p.1 * (a * b)⁻¹, j (a * b) • p.2⟩ : PairSp H G U) =
      ⟨a * (b * p.1 * b⁻¹) * a⁻¹, j a • j b • p.2⟩
    simp [mul_assoc, mul_smul]

private theorem out_eq_mul {G : Type} [Group G] (U : Subgroup G) (g : G) :
    ∃ u ∈ U, ((g : G ⧸ U).out : G) = g * u := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨h, h.2, hh⟩

private theorem pair_inv_mul_eq_of_mul_self_eq_one {H G : Type} [Group H] [Group G] (a b o u : G) (key : a⁻¹ * (b * a) = b) :
    (a * o * u)⁻¹ * b * (a * o * u) = u⁻¹ * (o⁻¹ * b * o) * u := by
  calc (a * o * u)⁻¹ * b * (a * o * u) = u⁻¹ * o⁻¹ * (a⁻¹ * (b * a)) * o * u := by group
    _ = u⁻¹ * (o⁻¹ * b * o) * u := by rw [key]; group

theorem UpperTheory.orbitalFiber_pair_correspondence :
    UpperTheory.V.Z.Sym.Glob.Fib.Pair := by
  classical
  intro H G I _ _ j H₀ U c f δ Hi _ φ hcen hfix hc hf hfin hT hidx hrange hδ hcov
  letI : MulAction H (PairSp H G U) := pairAct j U
  letI : MulAction H (G ⧸ U) := MulAction.compHom (G ⧸ U) j
  letI : ∀ i, MulAction (Hi i) (G ⧸ U) := fun i => MulAction.compHom (G ⧸ U) (j.comp (φ i))
  have hnorm : H₀.Normal := ⟨fun n hn g => by
    have hc' := Subgroup.mem_center_iff.1 (hcen hn) g
    rw [hc', mul_inv_cancel_right]
    exact hn⟩
  have hout : ∀ (a : G) (y : G ⧸ U), ∃ u ∈ U, ((a • y : G ⧸ U).out) = a * y.out * u := by
    intro a y
    have hy : (a • y : G ⧸ U) = ((a * y.out : G) : G ⧸ U) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [hy]
    exact out_eq_mul U _
  let K' : PairSp H G U → ℂ := fun p => c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)
  have hKinv : ∀ (h : H) (p : PairSp H G U), K' (h • p) = K' p := by
    intro h p
    obtain ⟨u, hu, he⟩ := hout (j h) p.2
    show c (h * p.1 * h⁻¹) * f ((j h • p.2).out⁻¹ * j (h * p.1 * h⁻¹) * (j h • p.2).out) =
      c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)
    rw [hc, he, map_mul, map_mul, map_inv]
    congr 1
    rw [show (j h * p.2.out * u)⁻¹ * (j h * j p.1 * (j h)⁻¹) * (j h * p.2.out * u) =
        u⁻¹ * (p.2.out⁻¹ * j p.1 * p.2.out) * u by group]
    exact hf u hu _
  have hfib : ∀ x : G ⧸ U, {p : PairSp H G U | p.2 = x ∧ K' p ≠ 0}.Finite := by
    intro x
    refine ((hfin x.out).image (fun γ => (⟨γ, x⟩ : PairSp H G U))).subset ?_
    rintro ⟨γ, y⟩ ⟨hy, hne⟩
    change y = x at hy
    subst hy
    exact ⟨γ, hne, rfl⟩
  obtain ⟨T, hTc⟩ := hT
  have hT'fin : (⋃ s ∈ T, {p : PairSp H G U | p.2 = (s : G ⧸ U) ∧ K' p ≠ 0}).Finite :=
    Set.Finite.biUnion T.finite_toSet (fun s _ => hfib _)
  have hcoverP : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ h : H, ∃ s ∈ hT'fin.toFinset, p = h • s := by
    intro p hp
    obtain ⟨γ0, s, hs, u, hu, he⟩ := hTc p.2.out
    refine ⟨γ0, γ0⁻¹ • p, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_iUnion₂]
      refine ⟨s, hs, ?_, ?_⟩
      · show j γ0⁻¹ • p.2 = (s : G ⧸ U)
        conv_lhs => rw [← QuotientGroup.out_eq' p.2, he]
        show ((j γ0⁻¹ * (j γ0 * s * u) : G) : G ⧸ U) = s
        rw [QuotientGroup.eq, map_inv]
        simpa [mul_assoc] using U.inv_mem hu
      · rw [hKinv]
        exact hp
    · rw [smul_smul, mul_inv_cancel, one_smul]
  have hfixP : ∀ z ∈ H₀, ∀ p : PairSp H G U, z • p = p := by
    intro z hz p
    obtain ⟨γ, y⟩ := p
    show (⟨z * γ * z⁻¹, j z • y⟩ : PairSp H G U) = ⟨γ, y⟩
    rw [← Subgroup.mem_center_iff.1 (hcen hz) γ, mul_inv_cancel_right, hfix z hz y]
  have hpush := UpperTheory.orbitalFiber_pushforward H (PairSp H G U) (G ⧸ U) H₀ (fun p => p.2) K' hnorm
    (fun _ _ => rfl) hfixP hKinv ⟨hT'fin.toFinset, hcoverP⟩ hfib (fun p _ => hidx p.2)
  have hfibsum : ∀ x : G ⧸ U, (∑ᶠ (p : PairSp H G U) (_ : p.2 = x), K' p) =
      ∑ᶠ γ : H, c γ * f (x.out⁻¹ * j γ * x.out) := by
    intro x
    have hr : ∀ p : PairSp H G U,
        (p.2 = x) = (p ∈ Set.range (fun γ : H => (⟨γ, x⟩ : PairSp H G U))) := by
      intro p
      apply propext
      constructor
      · intro hp
        exact ⟨p.1, by rw [← hp]⟩
      · rintro ⟨γ, rfl⟩
        rfl
    simp only [hr]
    rw [finsum_mem_range (fun a b hab => congrArg PairSp.fst hab)]
  have hcomm : ∀ i (a : Hi i), φ i a * δ i * (φ i a)⁻¹ = δ i := by
    intro i a
    rw [(hrange i (φ i a)).1 ⟨a, rfl⟩, mul_inv_cancel_right]
  have hequi : ∀ i (a : Hi i) (y : G ⧸ U),
      (⟨δ i, a • y⟩ : PairSp H G U) = φ i a • (⟨δ i, y⟩ : PairSp H G U) := by
    intro i a y
    show (⟨δ i, j (φ i a) • y⟩ : PairSp H G U) = ⟨φ i a * δ i * (φ i a)⁻¹, j (φ i a) • y⟩
    rw [hcomm]
  have hkiinv : ∀ i (a : Hi i) (y : G ⧸ U),
      c (δ i) * f ((a • y).out⁻¹ * j (δ i) * (a • y).out) = c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) := by
    intro i a y
    obtain ⟨u, hu, he⟩ := hout (j (φ i a)) y
    show c (δ i) * f ((j (φ i a) • y).out⁻¹ * j (δ i) * (j (φ i a) • y).out) = _
    rw [he, pair_inv_mul_eq_of_mul_self_eq_one (H := H) _ _ _ _ ?_, hf u hu]
    have h1 := (hrange i (φ i a)).1 ⟨a, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← h1, inv_mul_cancel_left]
  have hcovD : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ i, ∃ y : G ⧸ U, ∃ h : H,
      c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 ∧ p = h • (⟨δ i, y⟩ : PairSp H G U) := by
    rintro ⟨γ, y⟩ hp
    obtain ⟨i, h, hγ⟩ := hcov γ y.out hp
    refine ⟨i, j h⁻¹ • y, h, ?_, ?_⟩
    · have h2 := hKinv h⁻¹ ⟨γ, y⟩
      have h3 : h⁻¹ * γ * h⁻¹⁻¹ = δ i := by rw [hγ]; group
      change c (h⁻¹ * γ * h⁻¹⁻¹) * f ((j h⁻¹ • y).out⁻¹ * j (h⁻¹ * γ * h⁻¹⁻¹) * (j h⁻¹ • y).out) =
        K' ⟨γ, y⟩ at h2
      rw [h3] at h2
      rw [h2]
      exact hp
    · show (⟨γ, y⟩ : PairSp H G U) = ⟨h * δ i * h⁻¹, j h • j h⁻¹ • y⟩
      rw [← hγ, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have huniq : ∀ (i i' : I) (y y' : G ⧸ U) (h : H),
      c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 → c (δ i') * f (y'.out⁻¹ * j (δ i') * y'.out) ≠ 0 →
      h • (⟨δ i, y⟩ : PairSp H G U) = ⟨δ i', y'⟩ → i = i' ∧ h ∈ (φ i).range := by
    intro i i' y y' h _ _ he
    have h1 : h * δ i * h⁻¹ = δ i' := congrArg PairSp.fst he
    have hii := hδ i i' h h1.symm
    subst hii
    refine ⟨rfl, (hrange i h).2 ?_⟩
    calc h * δ i = h * δ i * h⁻¹ * h := by group
      _ = δ i * h := by rw [h1]
  have hdec := UpperTheory.orbitalFiber_decomposition H (PairSp H G U) I H₀ K' Hi (fun _ => G ⧸ U) φ
    (fun i y => (⟨δ i, y⟩ : PairSp H G U))
    (fun i y => c (δ i) * f (y.out⁻¹ * j (δ i) * y.out)) hnorm hKinv ⟨hT'fin.toFinset, hcoverP⟩
    hequi (fun _ _ _ hab => congrArg PairSp.snd hab) hkiinv (fun _ _ _ => rfl) hcovD huniq
  show gq H₀ (fun y : G ⧸ U => ∑ᶠ γ : H, c γ * f (y.out⁻¹ * j γ * y.out)) = _
  simp only [← hfibsum]
  rw [← hpush, hdec]
  apply finsum_congr
  intro i
  exact (UpperTheory.orbitalFiber_of_bot (Hi i) (G ⧸ U) (Subgroup.comap (φ i) H₀)
    (fun y => f (y.out⁻¹ * j (δ i) * y.out))).1 (c (δ i))
end

section
theorem UpperTheory.orbitalFiber_support_finite :
    UpperTheory.V.Z.Sym.Glob.Fib.SuppFin := by
  intro Γ G V _ _ _ _ B hB h0 f hf g
  have hK : Finite ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) := by
    have h := hB.stab g
    rw [h0, Subgroup.relIndex_bot_left] at h
    exact Nat.finite_of_card_ne_zero h
  have hKs : (((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι : Subgroup Γ) : Set Γ).Finite := Set.toFinite _
  have hfib : ∀ x : G ⧸ B.U, ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}).Finite := by
    intro x
    rcases Set.eq_empty_or_nonempty ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}) with he | ⟨γ₀, h₀⟩
    · rw [he]; exact Set.finite_empty
    · refine (hKs.image (fun k => γ₀ * k)).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩
      have e : ((g⁻¹ * B.ι γ₀ * g : G) : G ⧸ B.U) = ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U) :=
        (Set.mem_singleton_iff.1 h₀).trans (Set.mem_singleton_iff.1 hγ).symm
      refine ⟨_, QuotientGroup.eq.1 e, ?_⟩
      simp [mul_assoc]
  refine (hf.fin.preimage' (f := fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) fun x _ => hfib x).subset ?_
  intro γ hγ h
  apply hγ
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U (g⁻¹ * B.ι γ * g)
  have hr := hf.right u (g⁻¹ * B.ι γ * g)
  change f (((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U).out) = 0 at h
  change f (g⁻¹ * B.ι γ * g * u) = _ at hr
  rw [hu, hr] at h
  exact (mul_eq_zero.1 h).resolve_left (Units.ne_zero _)
end

section
open MulAction UpperTheory.V.Z.Sym

private theorem smul_quotient_eq_self_iff_exists_conj_out (G : Type) [Group G] (U : Subgroup G) (y : G ⧸ U) (a : G) :
    a • y = y ↔ ∃ u ∈ U, (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out y))) u = a := by
  set g := Quotient.out y with hg
  have hy : ((g : G) : G ⧸ U) = y := Quotient.out_eq y
  rw [← hy, MulAction.Quotient.smul_mk, QuotientGroup.eq]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, smul_eq_mul]
  constructor
  · intro h
    refine ⟨g⁻¹ * a * g, ?_, by group⟩
    have := inv_mem h
    simpa [mul_assoc] using this
  · rintro ⟨u, hu, rfl⟩
    have : (g * u * g⁻¹ * g)⁻¹ * g = u⁻¹ := by group
    rw [this]; exact inv_mem hu

theorem UpperTheory.symmetric_fiber_trace_kernel :
    UpperTheory.V.Z.Sym.Glob.Fib.TrKer := by
  intro Γ G V _ _ _ _ _ B hFin hω hΓ₀ f hf
  classical
  set s := Base.Tw.one B with hs
  let δ : ConjClasses Γ → Γ := fun i => Classical.choose (ConjClasses.exists_rep i)
  have hδ : ∀ i, ConjClasses.mk (δ i) = i := fun i => Classical.choose_spec (ConjClasses.exists_rep i)
  have hRel : ∀ a b : Γ, s.Rel a b ↔ IsConj a b := by
    intro a b
    simp only [Base.Tw.Rel, hs, Base.Tw.one, hΓ₀, Subgroup.mem_bot, MulEquiv.refl_apply, exists_eq_left, mul_one, isConj_iff]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x⁻¹, by group⟩
    · rintro ⟨c, rfl⟩; exact ⟨c⁻¹, by group⟩
  have hCent : ∀ (a x : Γ), x ∈ s.Cent a ↔ x * a = a * x := by
    intro a x
    show (∃ z ∈ B.Γ₀, x⁻¹ * a * (MulEquiv.refl Γ) x = a * z) ↔ _
    simp only [hΓ₀, Subgroup.mem_bot, exists_eq_left, mul_one, MulEquiv.refl_apply]
    constructor
    · intro h; calc x * a = x * (x⁻¹ * a * x) := by rw [h]
        _ = a * x := by group
    · intro h; calc x⁻¹ * a * x = x⁻¹ * (x * a) := by rw [mul_assoc, h]
        _ = a := by group
  have h2 : ∀ z ∈ (⊥ : Subgroup Γ), ∀ y : G ⧸ B.U, B.ι z • y = y := fun z hz y => by
    rw [Subgroup.mem_bot.mp hz, map_one, one_smul]
  have h3 : ∀ h γ : Γ, LinearMap.trace ℂ V (B.W (h * γ * h⁻¹)) = LinearMap.trace ℂ V (B.W γ) := fun h γ => by
    rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]
  have h4 : ∀ u ∈ B.U, ∀ g : G, f (u⁻¹ * g * u) = f g := fun u hu g => by
    have hl := hf.left ⟨u⁻¹, inv_mem hu⟩ (g * u)
    have hr := hf.right ⟨u, hu⟩ g
    simp only [hs, Base.Tw.one, MulEquiv.refl_apply, hω, MonoidHom.one_apply, Units.val_one, inv_one, one_mul] at hl hr
    rw [mul_assoc, hl, hr]
  have h5 : ∀ g : G, {γ | LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0}.Finite := fun g =>
    (UpperTheory.orbitalFiber_support_finite Γ G V B hFin hΓ₀ f hf g).subset (fun γ h => right_ne_zero_of_mul h)
  have h8 : ∀ i x, x ∈ ((s.Cent (δ i)).subtype).range ↔ x * δ i = δ i * x := fun i x => by
    rw [Subgroup.range_subtype, hCent]
  have h9 : ∀ (i i' : ConjClasses Γ) (h : Γ), δ i' = h * δ i * h⁻¹ → i = i' := fun i i' h e => by
    rw [← hδ i, ← hδ i', ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]; exact ⟨h, e.symm⟩
  have h10 : ∀ (γ : Γ) (g : G), LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0 →
      ∃ i h, γ = h * δ i * h⁻¹ := fun γ g _ => by
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ (ConjClasses.mk γ)))
    exact ⟨ConjClasses.mk γ, c, hc.symm⟩
  have h7 : ∀ y : G ⧸ B.U, (⊥ : Subgroup Γ).relIndex (Subgroup.comap B.ι (stabilizer G y)) ≠ 0 := fun y => by
    have := hFin.stab (Quotient.out y)
    rw [hΓ₀] at this
    convert this using 2
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, mem_stabilizer_iff, Subgroup.mem_map]
    exact smul_quotient_eq_self_iff_exists_conj_out G B.U y (B.ι x)
  have hT := (Tf.trace Γ G V B hFin s f hf (ConjClasses Γ) δ (fun i j h => by
      rw [← hδ i, ← hδ j, ConjClasses.mk_eq_mk_iff_isConj]; exact (hRel _ _).mp h)
    (fun γ _ => ⟨ConjClasses.mk γ, (hRel _ _).mpr (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ _))⟩)).2
  have hP := UpperTheory.orbitalFiber_pair_correspondence Γ G (ConjClasses Γ) B.ι ⊥ B.U (fun γ => LinearMap.trace ℂ V (B.W γ)) f δ
    (fun i => ↥(s.Cent (δ i))) (fun i => (s.Cent (δ i)).subtype) bot_le h2 h3 h4 h5
    hFin.cls h7 h8 h9 h10
  rw [hT, hP]
  refine finsum_congr fun i => ?_
  simp only [Base.Tw.term, hs, Base.Tw.one, LinearMap.comp_id]
  congr 2
  rw [hΓ₀]; rfl
end
