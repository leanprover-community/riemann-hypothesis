module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexScaledMaxIdealStatement

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.HeckeLatIndex

theorem ko_pres : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (κ : GL D k), κ ∈ KO k D → ∀ v : D → k, (∀ i, valuation k (v i) < 1) → ∀ i, valuation k (κ.1.mulVec v i) < 1 := by
  intro k _ _ _ _ D _ _ κ hκ v hv i
  have hent : ∀ j, valuation k (κ.1 i j) ≤ 1 := fun j =>
    (Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1 i j)
  rw [Matrix.mulVec, dotProduct]
  exact Valuation.map_sum_lt _ one_ne_zero fun j _ => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hent j)) (hv j)

theorem line_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (c : ℤ) (L P : AddSubgroup k), (∀ x, x ∈ L ↔ valuation k x < 1) → (∀ x, x ∈ P ↔ valuation k (((ϖ ^ c : kˣ) : k) * x) < 1) → (P ⊓ L).relIndex P * (P ⊓ L).relIndex L = resCard k ^ c.natAbs := GlobalTheory.T.relIndex_inf_mul_relIndex_inf_eq_resCard_pow

theorem relIndex_pi_univ {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

theorem diag_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (e : D → ℤ) (L P : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ P ↔ ∀ i, valuation k (((ϖ ^ e i : kˣ) : k) * v i) < 1) → (((P ⊓ L).relIndex P : ℕ) : ℝ) * (((P ⊓ L).relIndex L : ℕ) : ℝ) = (resCard k : ℝ) ^ (sumAbs e) := by
  intro k _ _ _ _ D _ _ ϖ hϖ e L P hL hP
  let L₀ : AddSubgroup k := (valuation k).ltAddSubgroup 1
  have hL₀ : ∀ x, x ∈ L₀ ↔ valuation k x < 1 := fun x => Iff.rfl
  let Pi : D → AddSubgroup k := fun i => L₀.comap (AddMonoidHom.mulLeft ((ϖ ^ e i : kˣ) : k))
  have hPi : ∀ i x, x ∈ Pi i ↔ valuation k (((ϖ ^ e i : kˣ) : k) * x) < 1 := fun i x => Iff.rfl
  have eL : L = AddSubgroup.pi Set.univ fun _ => L₀ := by
    ext v; rw [hL]; simp [AddSubgroup.mem_pi, hL₀]
  have eP : P = AddSubgroup.pi Set.univ Pi := by
    ext v; rw [hP]; simp [AddSubgroup.mem_pi, hPi]
  have eI : P ⊓ L = AddSubgroup.pi Set.univ fun i => Pi i ⊓ L₀ := by
    ext v; rw [AddSubgroup.mem_inf, eP, eL]; simp [AddSubgroup.mem_pi, forall_and]
  rw [eI, eP, eL, relIndex_pi_univ, relIndex_pi_univ]
  have h1 : ∀ i, (Pi i ⊓ L₀).relIndex (Pi i) * (Pi i ⊓ L₀).relIndex L₀ = resCard k ^ (e i).natAbs :=
    fun i => line_index k ϖ hϖ (e i) L₀ (Pi i) hL₀ (hPi i)
  rw [← Nat.cast_mul, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => h1 i),
    Finset.prod_pow_eq_pow_sum]
  have hs : sumAbs e = ((∑ i, (e i).natAbs : ℕ) : ℤ) := by
    unfold sumAbs; push_cast; simp [Int.natCast_natAbs]
  rw [hs, zpow_natCast]
  push_cast
  rfl

theorem map_eq_of_preimage {k : Type} [Field k] {D : Type} [Fintype D] [DecidableEq D] (g : GL D k)
    (S T : AddSubgroup (D → k)) (hS : ∀ w, w ∈ S ↔ g.1.mulVec w ∈ T) :
    S.map (Matrix.mulVecLin g.1).toAddMonoidHom = T := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hS w).1 hw
  · intro hv
    have hgv : g.1.mulVec ((g⁻¹).1.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨(g⁻¹).1.mulVec v, (hS _).2 (by rw [hgv]; exact hv), hgv⟩

theorem mulVec_injective {k : Type} [Field k] {D : Type} [Fintype D] [DecidableEq D] (g : GL D k) :
    Function.Injective (Matrix.mulVecLin g.1).toAddMonoidHom := by
  intro v w h
  have h' : (g⁻¹).1.mulVec (g.1.mulVec v) = (g⁻¹).1.mulVec (g.1.mulVec w) := congrArg _ h
  simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h'

theorem ko_mem_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : Type} [Fintype D] [DecidableEq D] (κ : GL D k) (hκ : κ ∈ KO k D) (L : AddSubgroup (D → k))
    (hL : ∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) (w : D → k) : w ∈ L ↔ κ.1.mulVec w ∈ L := by
  rw [hL, hL]
  refine ⟨ko_pres k D κ hκ w, fun h => ?_⟩
  have := ko_pres k D κ⁻¹ (inv_mem hκ) _ h
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

theorem ko_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (h κ κ' : GL D k), κ ∈ KO k D → κ' ∈ KO k D → ∀ (L P P' : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ P ↔ h.1.mulVec v ∈ L) → (∀ v, v ∈ P' ↔ (κ * h * κ').1.mulVec v ∈ L) → (P' ⊓ L).relIndex P' = (P ⊓ L).relIndex P ∧ (P' ⊓ L).relIndex L = (P ⊓ L).relIndex L := by
  intro k _ _ _ _ D _ _ h κ κ' hκ hκ' L P P' hL hP hP'
  have h1 : ∀ w, w ∈ P' ↔ κ'.1.mulVec w ∈ P := fun w => by
    rw [hP', hP, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← ko_mem_iff κ hκ L hL]
  have h2 : ∀ w, w ∈ L ↔ κ'.1.mulVec w ∈ L := ko_mem_iff κ' hκ' L hL
  have m1 := map_eq_of_preimage κ' P' P h1
  have m2 := map_eq_of_preimage κ' L L h2
  have hinj := mulVec_injective κ'
  constructor
  · rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf_eq _ _ _ hinj, m1, m2]
  · rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf_eq _ _ _ hinj, m1, m2]

end GlobalTheory.HeckeLatIndex
