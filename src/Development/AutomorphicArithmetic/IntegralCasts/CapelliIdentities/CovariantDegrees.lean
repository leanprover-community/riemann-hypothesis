module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.CovariantDegrees

noncomputable def jE : {l : ℕ} →
  [hl : Fact (Nat.Prime l)] →
    {E Ω : Type} → [inst : Field E] → [inst_1 : Field Ω] → [Algebra E Ω] → (Ω →+* PadicAlgCl l) → E →+* PadicAlgCl l :=
  fun {l} [Fact (Nat.Prime l)] {E Ω} [Field E] [Field Ω] [Algebra E Ω] j => j.comp (Algebra.algebraMap E Ω)

theorem aux2 : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E],
  Module.Free ℚ E := by
  intros; infer_instance

noncomputable def KwF : {l : ℕ} →
  [hl : Fact (Nat.Prime l)] →
    {E Ω : Type} →
      [inst : Field E] →
        [NumberField E] →
          [inst_2 : Field Ω] → [Algebra E Ω] → (Ω →+* PadicAlgCl l) → IntermediateField ℚ_[l] (PadicAlgCl l) :=
  fun {l} [Fact (Nat.Prime l)] {E Ω} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] j =>
    IntermediateField.adjoin ℚ_[l]
      (Set.range fun i => (jE j) ((Module.finBasis ℚ E) i))

@[reducible] noncomputable def G.{u_1, u_2} : (F : Type u_1) →
  (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
  fun F Ω [Field F] [Field Ω] [Algebra F Ω] => Gal(Ω/F)

noncomputable def Dec.{u_1, u_2} : {F : Type u_1} →
  {Ω : Type u_2} →
    [inst : Field F] →
      [inst_1 : Field Ω] →
        [inst_2 : Algebra F Ω] → ValuationSubring Ω → Subgroup (G F Ω) :=
  fun {F} {Ω} [Field F] [Field Ω] [Algebra F Ω] A => ValuationSubring.decompositionSubgroup F A

theorem aux6 : ∀ {E Ω : Type} [inst : Field E] [inst_1 : Field Ω]
  [inst_2 : Algebra E Ω], Module.IsTorsionFree E Ω := by
  intros; infer_instance

theorem aux7 : ∀ {Ω : Type} [inst : Field Ω] [inst_1 : CharZero Ω],
  Module.IsTorsionFree ℚ Ω := by
  intros; infer_instance

@[reducible] noncomputable def Om : (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
  fun l [Fact (Nat.Prime l)] => PadicAlgCl l

@[reducible] noncomputable def GQ : (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
  fun l [Fact (Nat.Prime l)] => Gal(Om l/ℚ_[l])

theorem laurent_T_neg_one_mul_T_one : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)],
  IsScalarTower ℚ ℚ_[l] (Om l) := by
  intros; infer_instance

theorem aux11 : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {Ω : Type}
  [inst : Field Ω] [inst_1 : CharZero Ω] (j : Ω →+* PadicAlgCl l),
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  IsScalarTower ℚ Ω (PadicAlgCl l) := by
  intro l hl Ω _ _ j
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem aux12 : ∀ {Ω : Type} [inst : Field Ω] [inst_1 : CharZero Ω]
  [IsAlgClosure ℚ Ω], Normal ℚ Ω := by
  intros; infer_instance

noncomputable def resQ : {l : ℕ} →
  [hl : Fact (Nat.Prime l)] →
    {Ω : Type} →
      [inst : Field Ω] →
        [inst_1 : CharZero Ω] →
          [IsAlgClosure ℚ Ω] → (Ω →+* PadicAlgCl l) → GQ l → Gal(Ω/ℚ) :=
  fun {l} [Fact (Nat.Prime l)] {Ω} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] j σ => by
    letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
    haveI := aux11 j
    exact (σ.restrictScalars ℚ).toAlgHom.restrictNormal' Ω

private theorem j_resQ {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l) (σ : GQ l) (x : Ω) :
    j (resQ j σ x) = σ (j x) := by
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI := aux11 j
  haveI : Normal ℚ Ω := aux12
  exact AlgHom.restrictNormal_commutes (σ.restrictScalars ℚ).toAlgHom Ω x

private theorem jE_mem {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (j : Ω →+* PadicAlgCl l) (x : E) :
    jE j x ∈ KwF (E := E) j := by

  rw [← (Module.finBasis ℚ E).sum_repr x, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

theorem zero_contDiffOn_supported : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)]
  {E Ω : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [inst_4 : CharZero Ω]
  [inst_5 : IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l),
  ∀ σ ∈ (KwF (E := E) j).fixingSubgroup,
    ∀ (x : E),
      (resQ j σ).toRingEquiv ((Algebra.algebraMap E Ω) x) =
        (Algebra.algebraMap E Ω) x := by
  intro l hl E Ω _ _ _ _ _ _ j σ hσ x
  apply j.injective
  refine (j_resQ j σ _).trans ?_
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (jE_mem j x)

noncomputable def resE : {l : ℕ} →
  [hl : Fact (Nat.Prime l)] →
    {E Ω : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          [inst_2 : Field Ω] →
            [inst_3 : Algebra E Ω] →
              [inst_4 : CharZero Ω] →
                [IsAlgClosure ℚ Ω] →
                  (j : Ω →+* PadicAlgCl l) →
                    (σ : GQ l) →
                      σ ∈ (KwF (E := E) j).fixingSubgroup →
                        G E Ω :=
  fun {l} [Fact (Nat.Prime l)] {E Ω} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] j σ
      hσ =>
    AlgEquiv.ofRingEquiv (zero_contDiffOn_supported j σ hσ)

private theorem j_resE {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)
    (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j (resE j σ hσ x) = σ (j x) :=
  j_resQ j σ x

open Pointwise in
private theorem resE_mem {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
    {A : ValuationSubring Ω} (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1)
    (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) :
    resE j σ hσ ∈ Dec (F := E) A := by
  have hn : ∀ x, ‖j (resE j σ hσ x)‖ = ‖j x‖ := fun x => by
    rw [j_resE]
    exact (spectralNorm_eq_of_equiv σ (j x)).symm
  refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hj, hj, ← hn]
  simp

theorem column_matrix_mul_inverse : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)]
  {E Ω : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
  {j : Ω →+* PadicAlgCl l} (σ : ↥(KwF (E := E) j).fixingSubgroup),
  ↑σ ∈ (KwF (E := E) j).fixingSubgroup := by
  intro l hl E Ω _ _ _ _ j σ
  exact σ.2

theorem complex_normed_instance_compat : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)]
  {E Ω : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω]
  [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω},
  (∀ (x : Ω), x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ (σ : ↥(KwF (E := E) j).fixingSubgroup),
      resE j (↑σ)
          (column_matrix_mul_inverse σ) ∈
        Dec (F := E) A := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj σ
  exact resE_mem hj _ _

theorem padic_embedding_algebra_compat : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)]
  {E Ω : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
  {j : Ω →+* PadicAlgCl l}, (1 : GQ l) ∈ (KwF (E := E) j).fixingSubgroup := by
  intro l hl E Ω _ _ _ _ j
  exact Subgroup.one_mem _

theorem blockM_one_partner_eq_one : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)]
  {E Ω : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω]
  [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω},
  (∀ (x : Ω), x ∈ A ↔ ‖j x‖ ≤ 1) →
    resE j 1
        padic_embedding_algebra_compat ∈
      Dec (F := E) A := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj
  exact resE_mem hj _ _

theorem blockM_mul_alt : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {E Ω : Type}
  [inst : Field E] [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [inst_4 : IsAlgClosure E Ω]
  [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
  (hj : ∀ (x : Ω), x ∈ A ↔ ‖j x‖ ≤ 1),
  (⟨resE j 1
        padic_embedding_algebra_compat,
      blockM_one_partner_eq_one hj⟩ : Dec (F := E) A) =
    1 := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj
  refine Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)
  exact j_resE (E := E) j 1 (Subgroup.one_mem _) x

theorem conj_invariant_character_mem : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)]
  {E Ω : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω]
  {j : Ω →+* PadicAlgCl l} (σ τ : ↥(KwF (E := E) j).fixingSubgroup),
  ↑(σ * τ) ∈ (KwF (E := E) j).fixingSubgroup := by
  intro l hl E Ω _ _ _ _ j σ τ
  exact (σ * τ).2

theorem rootGL_mem_unitary : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)]
  {E Ω : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω]
  [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω},
  (∀ (x : Ω), x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ (σ τ : ↥(KwF (E := E) j).fixingSubgroup),
      resE j (↑(σ * τ))
          (conj_invariant_character_mem σ τ) ∈
        Dec (F := E) A := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj σ τ
  exact resE_mem hj _ _

theorem conj_invariant_character_transport : ∀ {l : ℕ}
  [hl : Fact (Nat.Prime l)] {E Ω : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : Field Ω]
  [inst_3 : Algebra E Ω] [inst_4 : IsAlgClosure E Ω] [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω]
  {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω} (hj : ∀ (x : Ω), x ∈ A ↔ ‖j x‖ ≤ 1)
  (σ τ : ↥(KwF (E := E) j).fixingSubgroup),
  (⟨resE j (↑(σ * τ))
        (conj_invariant_character_mem σ τ),
      rootGL_mem_unitary hj σ τ⟩ : Dec (F := E) A) =
    ⟨resE j (↑σ)
          (column_matrix_mul_inverse σ),
        complex_normed_instance_compat hj σ⟩ *
      ⟨resE j (↑τ)
          (column_matrix_mul_inverse τ),
        complex_normed_instance_compat hj τ⟩ := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj σ τ
  refine Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)
  refine (j_resE j (σ * τ).1 (σ * τ).2 x).trans ?_
  refine Eq.symm ((j_resE j σ.1 σ.2 (resE j τ.1 τ.2 x)).trans ?_)
  rw [j_resE]
  rfl

noncomputable def rHom : {l : ℕ} →
  [hl : Fact (Nat.Prime l)] →
    {E Ω : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          [inst_2 : Field Ω] →
            [inst_3 : Algebra E Ω] →
              [IsAlgClosure E Ω] →
                [inst_5 : CharZero Ω] →
                  [IsAlgClosure ℚ Ω] →
                    {j : Ω →+* PadicAlgCl l} →
                      {A : ValuationSubring Ω} →
                        (∀ (x : Ω), x ∈ A ↔ ‖j x‖ ≤ 1) →
                          ↥(KwF (E := E) j).fixingSubgroup →*
                            ↥(Dec (F := E) A) :=
  fun {l} [Fact (Nat.Prime l)] {E Ω} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [CharZero Ω]
      [IsAlgClosure ℚ Ω] {j} {A} hj =>
    {
      toFun := fun σ =>
        ⟨resE j (↑σ)
            (column_matrix_mul_inverse σ),
          complex_normed_instance_compat hj σ⟩,
      map_one' := blockM_mul_alt hj,
      map_mul' := conj_invariant_character_transport hj }

theorem continuous_rHom : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {E Ω : Type}
  [inst : Field E] [inst_1 : NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [inst_4 : IsAlgClosure E Ω]
  [inst_5 : CharZero Ω] [inst_6 : IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
  (hj : ∀ (x : Ω), x ∈ A ↔ ‖j x‖ ≤ 1), Continuous ⇑(rHom (E := E) hj) := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj
  have h : Continuous ((Dec A).subtype.comp (rHom (E := E) hj)) := by
    apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).1 hs
    let b := Module.finBasis E L
    have hU : ∀ᶠ σ : (KwF (E := E) j).fixingSubgroup in nhds 1,
        ∀ i, σ.1 (j (b i)) = j (b i) := by
      refine Filter.eventually_all.2 fun i => ?_
      have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) (j (b i))).preimage
        (continuous_subtype_val (p := fun σ => σ ∈ (KwF (E := E) j).fixingSubgroup))
      exact ho.mem_nhds (Subgroup.one_mem (MulAction.stabilizer _ _))
    refine hU.mono fun σ hσ => hLs ?_
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have key : (resE j σ.1 σ.2).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
      b.ext fun i => j.injective ((j_resE j σ.1 σ.2 (b i)).trans (hσ i))
    exact LinearMap.congr_fun key ⟨x, hx⟩
  exact continuous_induced_rng.2 h

end UpperTheory.Reformulated.B.CovariantDegrees
