import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PolZCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LocSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.CountFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LcOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.CCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PsiCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FixCnt
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.ExistsCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualNO

section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem cnt {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (Z B : AddSubgroup X) [Finite Z] (hB : B ≤ Z) (f : X →+ Y)
    (hf : ∀ b ∈ B, f b = 0) (S : Set Y) (hS : ∀ s ∈ S, ∃ z ∈ Z, f z = s) :
    S.Finite ∧ S.ncard * Nat.card B ≤ (Z : Set X).ncard := by
  let g : Z →+ Y := f.comp Z.subtype
  haveI : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective
  have hsub : S ⊆ (g.range : Set Y) := fun s hs => by
    obtain ⟨z, hz, rfl⟩ := hS s hs
    exact ⟨⟨z, hz⟩, rfl⟩
  have hfin : (g.range : Set Y).Finite := Set.toFinite _
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 : S.ncard ≤ Nat.card g.range := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub hfin
  have h2 : Nat.card B ≤ Nat.card g.ker :=
    Nat.card_le_card_of_injective (fun b : B => (⟨⟨b.1, hB b.2⟩, hf b.1 b.2⟩ : g.ker))
      fun a b e => Subtype.ext (congrArg (fun t : g.ker => t.1.1) e)
  have h3 : Nat.card Z = Nat.card g.range * Nat.card g.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv]
  rw [← Nat.card_coe_set_eq (Z : Set X), SetLike.coe_sort_coe, h3]
  exact Nat.mul_le_mul h1 h2

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) :
    red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem UpperTheory.V.Th.selTr :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (rep : Representation O G.Γ (Mm O n m)), IsAd0 h y m rep → LC rep → Finite (Zl rep) → (trFun h y m '' Sel h y m).Finite ∧ (trFun h y m '' Sel h y m).ncard * Nat.card (Bl rep) ≤ {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}.ncard := by
  intro l _ L G G0 h O _ _ _ _ _ n y m rep hr hLC hF
  have hmul : ∀ g g', y.ρm h m (g * g') = y.ρm h m g * y.ρm h m g' := fun g g' => by
    simp only [Pt.ρm, map_mul, red_mul]
  have hone : y.ρm h m 1 = 1 := by simp only [Pt.ρm, map_one, red_one]
  have hrep : ∀ (g : G.G₀) Z, rep g Z = y.ρm h m g * Z * y.ρm h m g⁻¹ := fun g Z => (hr.1 g Z).trans (one_smul _ _)
  have hφ : ∀ v g, h.p₀ (G.φ v g) = G0.φ v g := fun v g => Subtype.ext (h.φ v g)
  have hρ : ∀ v g, y.ρm h m (G.φ v g) = y.ρ0 m (G0.φ v g) := fun v g => by rw [Pt.ρm, hφ]; rfl
  have hρ' : ∀ v g, y.ρm h m (G.φ v g)⁻¹ = y.ρ0 m (G0.φ v g)⁻¹ := fun v g => by rw [← map_inv, hρ, map_inv]
  let Z : AddSubgroup (G.Γ → Mm O n m) :=
    { carrier := {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}
      add_mem' := by
        rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
        exact ⟨add_mem a1 b1, fun v => add_mem (a2 v) (b2 v), fun u g hg => by rw [Pi.add_apply, a3 u g hg, b3 u g hg, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun v => zero_mem _, fun _ _ _ => rfl⟩
      neg_mem' := by
        rintro a ⟨a1, a2, a3⟩
        exact ⟨neg_mem a1, fun v => neg_mem (a2 v), fun u g hg => by rw [Pi.neg_apply, a3 u g hg, neg_zero]⟩ }
  haveI : Finite Z := Finite.of_injective (fun z : Z => (⟨z.1, z.2.1⟩ : Zl rep))
    fun a b e => Subtype.ext (congrArg (fun t : Zl rep => t.1) e)
  let f : (G.Γ → Mm O n m) →+ (G.G₀ → Om O m) :=
    { toFun := fun z => trFun h y m fun g => z g
      map_zero' := funext fun g => by simp [trFun]
      map_add' := fun a b => funext fun g => by simp [trFun, Matrix.add_mul] }
  refine cnt Z (Bl rep).toAddSubgroup (fun b hb => ?_) f (fun b hb => ?_) _ ?_
  · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hb
    obtain rfl : b = fun g => rep g Y - Y := funext hY
    refine ⟨⟨(hLC Y).comp (· - Y), fun g g' => by simp only [map_mul, Module.End.mul_apply, map_sub]; abel⟩,
      fun v => AddSubgroup.mem_sup_left ((mem_Bl _).2 ⟨Y, fun g => rfl⟩), fun u g hg => ?_⟩
    have e : y.ρ (h.p₀ (G.φu u g)) = 1 := y.ine u _ ⟨g, hg, Subtype.ext (h.φu u g).symm⟩
    have e1 : y.ρm h m (G.φu u g) = 1 := by rw [Pt.ρm, mat, MonoidHom.comp_apply, e, map_one, red_one]
    have e2 : y.ρm h m (G.φu u g)⁻¹ = 1 := by
      rw [Pt.ρm, map_inv, mat, MonoidHom.comp_apply, map_inv, e, inv_one, map_one, red_one]
    show rep (G.φu u g : G.G₀) Y - Y = 0
    rw [hrep, e1, e2, one_mul, mul_one, sub_self]
  · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hb
    funext g
    show (b g * y.ρm h m g).trace = 0
    rw [hY, hrep, sub_mul, mul_assoc _ _ (y.ρm h m g), ← hmul, inv_mul_cancel, hone, mul_one, Matrix.trace_sub,
      Matrix.trace_mul_comm, sub_self]
  · rintro _ ⟨z, ⟨z1, z2, z3, z4, z5⟩, rfl⟩
    have hP : IsUnit (red m (y.P : Matrix (Fin n) (Fin n) O)) :=
      ⟨⟨red m (y.P : Matrix (Fin n) (Fin n) O), red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O), by rw [← red_mul, Units.mul_inv, red_one],
        by rw [← red_mul, Units.inv_mul, red_one]⟩, rfl⟩
    obtain ⟨z', h1, -, h3⟩ := (polP l G.frame O (Om O m) n _ _ _ rep hP hr).1 z z1
      (fun g g' => by rw [one_smul]; exact z2 g g') (fun g => by rw [one_smul]; exact z3 g)
    refine ⟨z', ⟨h1, fun v => ?_, fun u g hg => (h3 _).trans (z4 u _ ⟨g, hg, rfl⟩)⟩, funext fun g => by
      show (z' g * _).trace = (z g * _).trace
      rw [h3]⟩
    obtain ⟨Y, hY⟩ := z5 v
    have hc : Continuous (G.η.ker.subtype.comp (G.φ v)) := continuous_subtype_val.comp (G.φ_cont v)
    have e : z' ∘ (G.η.ker.subtype.comp (G.φ v)) = (fun g => rep (G.φ v g : G.G₀) Y - Y) +
        fun g => z' (G.φ v g : G.G₀) - (rep (G.φ v g : G.G₀) Y - Y) := funext fun g => by simp
    rw [e]
    refine AddSubgroup.add_mem_sup ((mem_Bl _).2 ⟨Y, fun g => rfl⟩) ⟨?_, fun g g' => ?_, fun g => ?_⟩
    · exact (h1.1.comp_continuous hc).sub (((hLC Y).comp_continuous hc).comp (· - Y))
    · rw [← hρ, ← hρ', ← hrep]
      beta_reduce
      rw [map_mul, Subgroup.coe_mul, h1.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
      abel
    · have := (hY g).1
      rw [dY, ← hrep] at this
      simp only [h3]
      exact this
end

section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem natL (ZL B' M V U J A S' PV PU PJ K a b c1 c2 e f Sel B ci : ℕ) (hB : 0 < B') (hM : 0 < M)
    (h1 : ZL * B' * M ^ (V + (U + J)) * A ≤ M * S' * (PV * (PU * PJ))) (h2 : S' ≤ B' * K ^ c2)
    (h3 : PV * K ^ a ≤ M ^ V * K ^ e) (h4 : PU ≤ M ^ U) (h5 : PJ ≤ M ^ J * K ^ f) (h6 : K ^ b ≤ A)
    (h7 : Sel * B ≤ ZL) (h8 : B * ci = M) (h9 : ci ≤ K ^ c1) :
    Sel * K ^ (a + b) ≤ K ^ (c1 + c2 + e + f) := by
  have k1 : ZL * K ^ (a + b) * (B' * M ^ (V + (U + J))) ≤ M * K ^ (c2 + e + f) * (B' * M ^ (V + (U + J))) := by
    calc ZL * K ^ (a + b) * (B' * M ^ (V + (U + J))) = ZL * B' * M ^ (V + (U + J)) * K ^ b * K ^ a := by ring
      _ ≤ ZL * B' * M ^ (V + (U + J)) * A * K ^ a := by gcongr
      _ ≤ M * S' * (PV * (PU * PJ)) * K ^ a := by gcongr
      _ = M * S' * (PV * K ^ a) * PU * PJ := by ring
      _ ≤ M * (B' * K ^ c2) * (M ^ V * K ^ e) * M ^ U * (M ^ J * K ^ f) := by gcongr
      _ = M * K ^ (c2 + e + f) * (B' * M ^ (V + (U + J))) := by ring
  have k2 : ZL * K ^ (a + b) ≤ M * K ^ (c2 + e + f) := Nat.le_of_mul_le_mul_right k1 (by positivity)
  have hB0 : 0 < B := Nat.pos_of_mul_pos_right (h8 ▸ hM : 0 < B * ci)
  refine Nat.le_of_mul_le_mul_right (c := B) ?_ hB0
  calc Sel * K ^ (a + b) * B = Sel * B * K ^ (a + b) := by ring
    _ ≤ ZL * K ^ (a + b) := by gcongr
    _ ≤ B * ci * K ^ (c2 + e + f) := by rw [h8]; exact k2
    _ ≤ B * K ^ c1 * K ^ (c2 + e + f) := by gcongr
    _ = K ^ (c1 + c2 + e + f) * B := by ring

private theorem block_le₂ {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (h : LC ρ) : (Bl ρ).toAddSubgroup ≤ (Zl ρ).toAddSubgroup := by
  intro z hz
  obtain ⟨m, hm⟩ := (mem_Bl ρ).1 hz
  have : z = fun g => ρ g m - m := funext hm
  subst this
  refine (mem_Zl ρ).2 ⟨(h m).comp (fun y => y - m), fun g g' => ?_⟩
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel

private theorem lc_comp {R Γ D M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group D] [TopologicalSpace D]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (h : LC ρ) (φ : D →* Γ) (hφ : Continuous φ) :
    LC (ρ.comp φ : Representation R D M) := fun m => (h m).comp_continuous hφ

private theorem zl_comp {R Γ D M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group D] [TopologicalSpace D]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (φ : D →* Γ) (hφ : Continuous φ) {z : Γ → M}
    (hz : z ∈ Zl ρ) : z ∘ φ ∈ Zl (ρ.comp φ : Representation R D M) :=
  ⟨hz.1.comp_continuous hφ, fun g g' => by simp [hz.2]⟩

theorem UpperTheory.V.Th.oneLevelO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (q d : ℕ) (a : ArData G q d) (rep rep' : Representation O G.Γ (Mm O n m)) (e : L.Vl → ℕ) (f : Option (Fin q) → ℕ) (c₁ c₂ : ℕ), l ≠ 2 → Cnts a → IsAd0 h y m rep → IsAd1 h y m rep' → (∀ v, Finite (Zbor y m v) ∧ Nat.card (Zbor y m v) ≤ Nat.card (ResidueField O) ^ e v) → (∀ j, Nat.card (Representation.invariants (rep'.comp (a.ι (.inr (.inr j))) : Representation O (a.D (.inr (.inr j))) _)) ≤ Nat.card (ResidueField O) ^ f j) → Nat.card rep.invariants ≤ Nat.card (ResidueField O) ^ c₁ → (Finite (Zl rep') → {z | z ∈ Zl rep' ∧ ∀ j : Fin q, z ∘ a.ι (.inr (.inr (some j))) ∈ Bl (rep'.comp (a.ι (.inr (.inr (some j)))) : Representation O (a.D (.inr (.inr (some j)))) _)}.ncard ≤ Nat.card (Bl rep') * Nat.card (ResidueField O) ^ c₂) → (trFun h y m '' Sel h y m).Finite ∧ (trFun h y m '' Sel h y m).ncard * Nat.card (ResidueField O) ^ (m * (n + n.choose 2) * Fintype.card L.Vl + m * n.choose 2 * d) ≤ Nat.card (ResidueField O) ^ (c₁ + c₂ + ∑ v, e v + ∑ j, f j) := by
  intro l _ L G G0 h O _ _ _ _ _ n y m q d a rep rep' e f c₁ c₂ hl hC hrep hrep' hZb hf hc1 hc2
  classical
  obtain ⟨h2, hOm⟩ := omFacts l O
  obtain ⟨hfD, -, hlD, -⟩ := hOm m
  haveI := hfD
  haveI : Finite (Mm O n m) := inferInstanceAs (Finite (Fin n → Fin n → Om O m))
  obtain ⟨k, b, hk, hb⟩ := pairP l L G G0 h O n y m a.c_ε
  have hb := hb rep rep' hrep hrep'
  have hLC : LC rep := (adExP l L G G0 h O n y m).2.2 rep (Or.inl hrep)
  have hι : ∀ w, Continuous (a.ι w) := by
    rintro (v | u | j)
    · exact continuous_subtype_val.comp (G.φ_cont v)
    · exact continuous_subtype_val.comp (G.φu_cont u)
    · exact continuous_subtype_val.comp (a.φq_cont j)
  have hLCw : ∀ w, LC (rep.comp (a.ι w) : Representation O (a.D w) _) := fun w => lc_comp rep hLC _ (hι w)
  have hpu : ∀ u g, h.p₀ (G.φu u g) = G0.φu u g := fun u g => Subtype.ext (h.φu u g)
  have hρ : ∀ u, ∀ g ∈ L.Ju u, y.ρm h m (G.φu u g) = 1 := fun u g hg => by
    have h1 : y.ρ (G0.φu u g) = 1 := y.ine u _ ⟨g, hg, rfl⟩
    have h3 : mat y.ρ (G0.φu u g) = 1 := congrArg Units.val h1
    rw [Pt.ρm, hpu, h3, red]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hu : ∀ u, ∀ g ∈ L.Ju u, rep (G.φu u g : G.Γ) = 1 := fun u g hg => by
    refine LinearMap.ext fun Z => ?_
    have := hrep.1 (G.φu u g) Z
    have e1 := hρ u g⁻¹ (inv_mem hg)
    rw [map_inv] at e1
    rw [hρ u g hg, one_smul, one_mul] at this
    exact this.trans ((congrArg (Z * ·) e1).trans (mul_one Z))
  let 𝓛 : ∀ w, AddSubgroup (a.D w → Mm O n m) := fun w => match w with
    | .inl v => (Bl (rep.comp (a.ι (.inl v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v
    | .inr (.inl u) => (Zl (rep.comp (a.ι (.inr (.inl u))) : Representation O (L.Gu u) _)).toAddSubgroup ⊓
        AddSubgroup.pi (L.Ju u : Set (L.Gu u)) (fun _ => ⊥)
    | .inr (.inr j) => (Zl (rep.comp (a.ι (.inr (.inr j))) : Representation O (a.Dq j) _)).toAddSubgroup
  have hloc := fun v => locSup l L G G0 h O n y m rep v hrep hLC (hZb v).1
  have h𝓛 : ∀ w, (Bl (rep.comp (a.ι w) : Representation O (a.D w) _)).toAddSubgroup ≤ 𝓛 w ∧
      𝓛 w ≤ (Zl (rep.comp (a.ι w) : Representation O (a.D w) _)).toAddSubgroup := by
    rintro (v | u | j)
    · exact ⟨le_sup_left, (hloc v).1⟩
    · refine ⟨le_inf (block_le₂ _ (hLCw _)) fun z hz g hg => ?_, inf_le_left⟩
      obtain ⟨Y, hy⟩ := (mem_Bl _).1 hz
      have e1 : rep (G.φu u g : G.Γ) Y - Y = 0 := by rw [hu u g hg]; simp
      exact AddSubgroup.mem_bot.2 ((hy g).trans e1)
    · exact ⟨block_le₂ _ (hLCw _), le_rfl⟩
  obtain ⟨hF, hF', hgw⟩ := hC.gw k hk O _ _ rep rep' b hLC hb 𝓛 h𝓛
  obtain ⟨hS1, hS2⟩ := selTr l L G G0 h O n y m rep hrep hLC hF
  have hS3 := (cCount O G.Γ (Mm O n m) rep G.c G.c_sq (h2 hl)).2.1
  refine ⟨hS1, ?_⟩
  have hFs : (Zl rep : Set (G.Γ → Mm O n m)).Finite := Set.toFinite _
  have hFs' : (Zl rep' : Set (G.Γ → Mm O n m)).Finite := Set.toFinite _
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.card_sum, Fintype.card_sum] at hgw
  haveI : Finite (Bl rep') := Finite.of_surjective _ (LinearMap.surjective_rangeRestrict _)
  refine natL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Nat.card_pos Nat.card_pos hgw ?_ ?_ ?_ ?_ ?_
    (hS2.trans ?_) hS3 hc1
  · refine le_trans (Set.ncard_le_ncard ?_ (hFs'.subset fun y hy => hy.1)) (hc2 hF')
    exact fun y hy => ⟨hy.1, fun j => hy.2 _ rfl⟩
  · rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun v _ => ?_
    exact le_trans (hloc v).2.2 (Nat.mul_le_mul_left _ (hZb v).2)
  · rw [← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod' fun u _ => ?_
    have := (hC.unr u m O _ (rep.comp (a.ι (.inr (.inl u)))) (hLCw _) (fun Y => Matrix.ext fun i j => hlD (Y i j)) (hu u)).2
    rw [← Nat.card_coe_set_eq] at this
    exact this
  · rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun j _ => ?_
    have := (hC.locQ j k hk O _ _ (rep.comp (a.ι (.inr (.inr j)))) (rep'.comp (a.ι (.inr (.inr j)))) b (hLCw _)
      ⟨hb.left, hb.right, fun g y z => hb.equiv _ y z⟩).2
    rw [add_zero, pow_one] at this
    exact this.le.trans (Nat.mul_le_mul_left _ (hf j))
  · rw [pow_mul]
    conv_lhs => rw [← Fintype.card_fin d, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun i _ =>
      pow_choose_two_le_card_fixed_ad0_of_odd_involution l L G G0 h O n y m rep _ hl hrep (a.cw_sq i) (a.cw_η i)
  · refine Set.ncard_le_ncard ?_ (hFs.subset fun y hy => hy.1)
    rintro z ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    rintro (v | u | j)
    · exact h2 v
    · exact ⟨zl_comp rep _ (hι _) h1, fun g hg => h3 u g hg⟩
    · exact zl_comp rep _ (hι _) h1
end

section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem red_mul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_sub' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A - B) = red m A - red m B := by
  ext i j
  simp [red]

private theorem red_surj {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (Y : Mm O n m) : ∃ Y', red m Y' = Y := by
  choose Y' hY' using fun i j => Ideal.Quotient.mk_surjective (Y i j)
  exact ⟨Matrix.of Y', by ext i j; exact hY' i j⟩

private theorem red_add' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A + B) = red m A + red m B := by
  ext i j
  simp [red]

theorem UpperTheory.V.Th.h0GO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n), l ≠ 2 → ∃ C : ℕ, ∀ m, {Y : Mm O n m | red m y.P * Y = -(Yᵀ * red m y.P) ∧ ∀ g, y.ρ0 m g * Y * y.ρ0 m g⁻¹ = Y}.ncard ≤ Nat.card (ResidueField O) ^ C := by
  intro l _ L G0 O _ _ _ hO _ n y hl
  have h2u : IsUnit (2 : O) := (omFacts l O).1 hl
  let Φ : Option G0.G₀ → Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O := fun s => s.elim
    (LinearMap.mulLeft O (y.P : Matrix (Fin n) (Fin n) O) + (LinearMap.mulRight O (y.P : Matrix (Fin n) (Fin n) O)).comp
      (Matrix.transposeLinearEquiv (Fin n) (Fin n) O O).toLinearMap)
    fun g => (LinearMap.mulRight O (mat y.ρ g⁻¹)).comp (LinearMap.mulLeft O (mat y.ρ g)) - LinearMap.id
  have hΦ0 : ∀ Y, Φ none Y = (y.P : Matrix (Fin n) (Fin n) O) * Y + Yᵀ * y.P := fun _ => rfl
  have hΦ : ∀ g Y, Φ (some g) Y = mat y.ρ g * Y * mat y.ρ g⁻¹ - Y := fun _ _ => rfl
  obtain ⟨C, hC⟩ := fixCnt l O n _ Φ
  have hk : (⨅ g, LinearMap.ker (Φ g) : Submodule O (Matrix (Fin n) (Fin n) O)) = ⊥ := by
    refine eq_bot_iff.2 fun Y hY => ?_
    obtain ⟨c, hc, hsp⟩ := y.span
    have h1 : ∀ Z ∈ Submodule.span O (Set.range (mat y.ρ)), Z * Y = Y * Z := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem Z hZ =>
        obtain ⟨g, rfl⟩ := hZ
        have h1 : Φ (some g) Y = 0 := (Submodule.mem_iInf _).mp hY (some g)
        rw [hΦ, sub_eq_zero] at h1
        have h2 := congrArg (· * mat y.ρ g) h1
        simpa only [Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one] using h2
      | zero => simp
      | add a b _ _ ha hb => rw [Matrix.add_mul, Matrix.mul_add, ha, hb]
      | smul a b _ hb => rw [Matrix.smul_mul, Matrix.mul_smul, hb]
    have h2 : ∀ Z, Z * Y = Y * Z := fun Z => by
      have := h1 _ (hsp Z)
      rw [Matrix.smul_mul, Matrix.mul_smul] at this
      exact smul_right_injective _ hc this
    obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_single (M := Y) fun i j _ => h2 _
    have h3 : Φ none Y = 0 := (Submodule.mem_iInf _).mp hY none
    have hs : Y = a • (1 : Matrix (Fin n) (Fin n) O) := by
      rw [← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have ht : Yᵀ = Y := by rw [hs, Matrix.transpose_smul, Matrix.transpose_one]
    rw [hΦ0, ht, h2, ← two_smul O, h2u.smul_eq_zero] at h3
    exact (Units.mul_left_eq_zero y.P).1 h3
  refine ⟨C, fun m => ?_⟩
  have := hC m
  rw [hk, finrank_bot, mul_zero, zero_add] at this
  refine le_trans (le_of_eq (congrArg Set.ncard ?_)) this
  have ht : ∀ Y : Matrix (Fin n) (Fin n) O, red m Yᵀ = (red m Y)ᵀ := fun _ => rfl
  ext Y
  constructor
  · rintro ⟨h0, hY⟩
    obtain ⟨Y', e⟩ := red_surj m Y
    refine ⟨Y', e, ?_⟩
    rintro (_ | g)
    · rw [hΦ0, red_add', red_mul', red_mul', ht, e, h0, neg_add_cancel]
    · rw [hΦ, red_sub', red_mul', red_mul', e]
      exact sub_eq_zero.mpr (hY g)
  · rintro ⟨Y', e, h⟩
    refine ⟨?_, fun g => ?_⟩
    · have h1 := h none
      rw [hΦ0, red_add', red_mul', red_mul', ht, e] at h1
      exact eq_neg_of_add_eq_zero_left h1
    · have h1 := h (some g)
      rw [hΦ, red_sub', red_mul', red_mul', e] at h1
      exact sub_eq_zero.mp h1
end

section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem card_inv_le {A M Γ : Type} [CommRing A] [AddCommGroup M] [Module A M] [Finite M] [Group Γ]
    (r : Representation A Γ M) (S : Set M)
    (h : ∀ y : M, (∀ g, r g y = y) → y ∈ S) : Nat.card r.invariants ≤ S.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective (fun y : r.invariants => (⟨y.1, h y.1 y.2⟩ : S))
    fun a b e => Subtype.ext (congrArg (fun z : S => z.1) e)

private theorem cancel_pow {s K u w : ℕ} (hK : 0 < K) (h : s * K ^ u ≤ K ^ (w + u)) : s ≤ K ^ w := by
  rw [pow_add] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos hK u)

private theorem sum_exp {V : Type} [Fintype V] (m n ν d q c₁ c₂ c₀ : ℕ) (dv C : V → ℕ) (Cq : Fin q → ℕ)
    (h2 : ∑ v, dv v = d) :
    c₁ + c₂ + ∑ v, (m * ((n + ν) * (1 + dv v)) + C v) +
      ∑ j : Option (Fin q), (j.elim c₀ fun i => m * n + Cq i) =
    (m * (n * d + n * q) + (c₁ + c₂ + c₀ + ∑ v, C v + ∑ j, Cq j)) + (m * (n + ν) * Fintype.card V + m * ν * d) := by
  rw [Fintype.sum_option]
  simp only [Option.elim, Finset.sum_add_distrib, ← Finset.mul_sum, h2, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  ring

private theorem residual_rep_one {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} (y : Pt G0.frame O n) (m : ℕ) : y.ρ0 m 1 = 1 := by
  simp [Pt.ρ0, red, mat]

private theorem residual_rep_mul {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} (y : Pt G0.frame O n) (m : ℕ) (g h : G0.G₀) :
    y.ρ0 m (g * h) = y.ρ0 m g * y.ρ0 m h := by
  simp [Pt.ρ0, red, mat, Matrix.map_mul]

theorem UpperTheory.V.Th.b1absO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (al : Fin T.q → Fin n → O) (d : ℕ) (D0 : Subgroup G0.G₀) (_ : Sys T d D0), l ≠ 2 → PhiCond G0.Γ l → (∀ v, ∃ g, algebraMap ℤ_[l] O (G0.ε (G0.φ v g) : ℤ_[l]) ≠ 1) → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → y.N4 D0 → Eig y T al → DetO y (Set.range T.sg) → B1 y T (n * d + n * T.q) := by
  intro l _ L G0 T O _ _ _ _ _ n y al d D0 S hl hΦ hε hPL hN4 hE hD
  classical
  have hloc : ∀ v : L.Vl, LocCnt (L.Gv v) (G0.ε.comp (G0.η.ker.subtype.comp (G0.φ v))) (S.dv v) := fun v => by
    have h1 := (S.counts 0).locV v
    rw [S.dv_eq 0] at h1
    have h2 : (T.GN 0).ε.comp ((S.a 0).ι (.inl v)) = G0.ε.comp (G0.η.ker.subtype.comp (G0.φ v)) := by
      refine MonoidHom.ext fun g => ?_
      show (T.GN 0).ε ((T.GN 0).φ v g) = G0.ε (G0.φ v g)
      rw [← (T.h 0).φ v g, (T.h 0).ε]
    exact h2 ▸ h1
  have hc : G0.ε G0.c = -1 := by rw [← (T.h 0).c, (T.h 0).ε]; exact (S.a 0).c_ε
  choose Cv hCv using fun v : L.Vl => locVO l L G0 O n y v (S.dv v) (hloc v) (hε v)
  obtain ⟨c₁, hc₁⟩ := h0GO l L G0 O n y hl
  obtain ⟨c₀, hc₀⟩ := h0v0O l L G0 O n y D0 hN4
  choose Cq hCq using fun j : Fin T.q => h0qO l L G0 O n y (T.sg j) (al j) (hE j).1 (hE j).2
  obtain ⟨c₂, hc₂⟩ := dualNO l L G0 T O n y hl hc hΦ hPL hD
  refine ⟨c₁ + c₂ + c₀ + ∑ v, Cv v + ∑ j, Cq j, fun m => ?_⟩
  filter_upwards [hc₂ m, phEqO l L G0 T O n y m hΦ hPL] with N hN hP
  haveI : Finite (Om O m) := ((omFacts l O).2 m).1
  have hK : 0 < Nat.card (ResidueField O) := by
    have h1 := ((omFacts l O).2 1)
    haveI := h1.1
    have h2 := h1.2.1
    rw [pow_one] at h2
    rw [← h2]
    exact Nat.card_pos
  obtain ⟨⟨rep, hr⟩, ⟨rep', hr'⟩, -⟩ := adExP l L (T.GN N) G0 (T.h N) O n y m
  have hm : ∀ g, y.ρm (T.h N) m g = y.ρ0 m ((T.h N).p₀ g) := fun _ => rfl
  have he : ∀ g, epsm O (T.GN N) m g = epsm O G0 m ((T.h N).p g) := fun g => by
    simp only [epsm, (T.h N).ε]
  have key := oneLevelO l L (T.GN N) G0 (T.h N) O n y m T.q d (S.a N) rep rep'
    (fun v => m * ((n + n.choose 2) * (1 + S.dv v)) + Cv v)
    (fun j => j.elim c₀ fun i => m * n + Cq i) c₁ c₂ hl (S.counts N) hr hr' (fun v => hCv v m) ?_ ?_ ?_
  · have h2 : ∑ v, S.dv v = d := by rw [← S.dv_eq N]; exact (S.a N).sum_dv
    have k2 := key.2
    rw [sum_exp m n (n.choose 2) d T.q c₁ c₂ c₀ S.dv Cv Cq h2] at k2
    exact ⟨key.1, cancel_pow hK k2⟩
  · rintro (_ | j)
    · refine le_trans (card_inv_le _ _ ?_) (hc₀ m)
      intro Y hy g hg
      rw [← S.d0 N] at hg
      obtain ⟨γ, rfl⟩ := hg
      have e1 := hr'.1 ((S.a N).φq none γ) Y
      have e2 : rep' ((S.a N).φq none γ : (T.GN N).G₀) Y = Y := hy γ
      rw [e2, hm, hm, he, map_inv] at e1
      exact e1.symm
    · refine le_trans (card_inv_le _ _ ?_) (hCq j m)
      intro Y hy
      obtain ⟨γ, hγ⟩ := S.ph N j
      have e1 := hr'.1 (T.ph N j) Y
      have e2 : rep' (T.ph N j : (T.GN N).G₀) Y = Y := by rw [← hγ]; exact hy γ
      rw [e2, hm, hm, he, map_inv] at e1
      have e3 : y.ρ0 m ((T.h N).p₀ (T.ph N j))⁻¹ = y.ρ0 m (T.sg j)⁻¹ := by
        have a1 := residual_rep_mul y m ((T.h N).p₀ (T.ph N j))⁻¹ ((T.h N).p₀ (T.ph N j))
        have a2 := residual_rep_mul y m (T.sg j) (T.sg j)⁻¹
        rw [inv_mul_cancel, residual_rep_one, (hP j).1] at a1
        rw [mul_inv_cancel, residual_rep_one] at a2
        exact left_inv_eq_right_inv a1.symm a2.symm
      rw [(hP j).1, (hP j).2.1, one_smul, e3] at e1
      exact e1.symm
  · refine le_trans (card_inv_le _ _ ?_) (hc₁ m)
    intro Y hy
    refine ⟨?_, fun g => ?_⟩
    · have e1 := hr.2 Y
      have e2 : rep (T.GN N).frame.c Y = Y := hy _
      rw [e2, one_smul] at e1
      exact e1
    · obtain ⟨γ, hγ⟩ := (T.h N).surj g
      have hγm : γ ∈ (T.GN N).η.ker := by
        rw [MonoidHom.mem_ker, ← (T.h N).η, hγ]; exact g.2
      have e0 : (T.h N).p₀ ⟨γ, hγm⟩ = g := Subtype.ext hγ
      have e1 := hr.1 ⟨γ, hγm⟩ Y
      have e2 : rep ((⟨γ, hγm⟩ : (T.GN N).G₀) : (T.GN N).Γ) Y = Y := hy _
      rw [e2, hm, hm, map_inv, e0, one_smul] at e1
      exact e1.symm
  · intro hF
    refine le_trans (Set.ncard_le_ncard ?_ ?_) (hN rep' hr' hF)
    · rintro z ⟨h1, h2⟩
      refine ⟨h1, fun j => ?_⟩
      obtain ⟨Y, hY⟩ := (mem_Bl _).1 (h2 j)
      obtain ⟨γ, hγ⟩ := S.ph N j
      obtain ⟨δ, hδ⟩ := S.ta N j
      exact ⟨Y, by rw [← hγ]; exact hY γ, by rw [← hδ]; exact hY δ⟩
    · exact (Set.toFinite ((Zl rep' : Set _))).subset fun z hz => hz.1
end
