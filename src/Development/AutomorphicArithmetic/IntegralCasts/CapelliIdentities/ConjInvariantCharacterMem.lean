module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

namespace UpperTheory.Reformulated.B.Yzd4

noncomputable def cT : {A : Type} →
  [inst : CommRing A] → (A →+* A) → {m p : Type} → Matrix m p A → Matrix p m A :=
  fun {A} [CommRing A] σ {m p} M => (M.map ⇑σ).transpose

private theorem cT_mul {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (a b : Matrix n n A) :
    cT σ (a * b) = cT σ b * cT σ a := by
  simp only [cT]
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_one {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) : cT σ (1 : Matrix n n A) = 1 := by
  simp only [cT]
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem aux2 : ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n]
  [inst_2 : DecidableEq n] (σ : A →+* A) (J : Matrix n n A) {a b : GL n A},
  a ∈ {g : GL n A | cT σ g.val * J * g.val = J} →
    b ∈ {g : GL n A | cT σ g.val * J * g.val = J} →
      a * b ∈ {g : GL n A | cT σ g.val * J * g.val = J} := by
  intro A _ n _ _ σ J a b ha hb
  have ha' : cT σ (a : Matrix n n A) * J * (a : Matrix n n A) = J := ha
  have hb' : cT σ (b : Matrix n n A) * J * (b : Matrix n n A) = J := hb
  change cT σ ((a * b : Matrix.GeneralLinearGroup n A) : Matrix n n A) * J *
    ((a * b : Matrix.GeneralLinearGroup n A) : Matrix n n A) = J
  rw [Units.val_mul, cT_mul]
  calc _ = cT σ (b : Matrix n n A) *
        (cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [ha', hb']

theorem aux3 : ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n]
  [inst_2 : DecidableEq n] (σ : A →+* A) (J : Matrix n n A), cT σ (1 : GL n A).val * J * (1 : GL n A).val = J := by
  intro A _ n _ _ σ J
  rw [Units.val_one, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem aux4 : ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n]
  [inst_2 : DecidableEq n] (σ : A →+* A) (J : Matrix n n A) {g : GL n A},
  g ∈ {g : GL n A | cT σ g.val * J * g.val = J} →
    g⁻¹ ∈ {g : GL n A | cT σ g.val * J * g.val = J} := by
  intro A _ n _ _ σ J g hg
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  change cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) * J *
    ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) = J
  have h1 : (g : Matrix n n A) * ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) = 1 :=
    Units.mul_inv g
  have h2 : cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) *
      cT σ (g : Matrix n n A) = 1 := by
    rw [← cT_mul, h1, cT_one]
  calc _ = cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) *
        (cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *
        ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) := by rw [hg']
    _ = (cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) *
        cT σ (g : Matrix n n A)) * J *
        ((g : Matrix n n A) * ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

noncomputable def UJ : {A : Type} →
  [inst : CommRing A] →
    {n : Type} → [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → (A →+* A) → Matrix n n A → Subgroup (GL n A) :=
  fun {A} [inst : CommRing A] {n} [inst_1 : Fintype n] [inst_2 : DecidableEq n] σ J =>
    { carrier := {g : GL n A | cT σ g.val * J * g.val = J},
      mul_mem' := @aux2 A inst n inst_1 inst_2 σ J,
      one_mem' := aux3 σ J,
      inv_mem' := @aux4 A inst n inst_1 inst_2 σ J }

theorem aux6 : ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R]
  [inst_2 : Algebra F R], SMulCommClass F F R := by
  intro F _ R _ _
  exact inferInstance

theorem aux7 : ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R]
  [inst_2 : Algebra F R], IsScalarTower F F R := by
  intro F _ R _ _
  exact inferInstance

noncomputable def sigR : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] → [inst_4 : Algebra F R] → (E →ₐ[F] E) → TensorProduct F R E →+* TensorProduct F R E :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] σ =>
    (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom

theorem aux9 : ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R]
  [inst_2 : Algebra F R], SMulCommClass F R R := by
  intro F _ R _ _
  exact inferInstance

theorem laurent_T_neg_one_mul_T_one : ∀ {F : Type} [inst : Field F] (R : Type)
  [inst_1 : CommRing R] [inst_2 : Algebra F R], IsScalarTower F R R := by
  intro F _ R _ _
  exact inferInstance

theorem aux11 : ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E], SMulCommClass F E E := by
  intro F E _ _ _
  exact inferInstance

theorem aux12 : ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E], IsScalarTower F E E := by
  intro F E _ _ _
  exact inferInstance

noncomputable def inclR : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) → [inst_3 : CommRing R] → [inst_4 : Algebra F R] → E →+* TensorProduct F R E :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] => Algebra.TensorProduct.includeRight.toRingHom

noncomputable def JR : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] →
            [inst_4 : Algebra F R] →
              {M : ℕ} → Matrix (Fin M) (Fin M) E → Matrix (Fin M) (Fin M) (TensorProduct F R E) :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] {M} J =>
    J.map ⇑(inclR R)

noncomputable def HR : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] →
            [inst_4 : Algebra F R] →
              (E →ₐ[F] E) → {M : ℕ} → Matrix (Fin M) (Fin M) E → Subgroup (GL (Fin M) (TensorProduct F R E)) :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] σ {M} J =>
    UJ (sigR R σ) (JR R J)

noncomputable def HA : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) → [inst_3 : CommRing R] → [Algebra F R] → (E →ₐ[F] E) → {M : ℕ} → Matrix (Fin M) (Fin M) E → Type :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] σ {M} J =>
    ↥(HR R σ J)

noncomputable def topTens : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] →
            [inst_4 : Algebra F R] → [TopologicalSpace R] → TopologicalSpace (TensorProduct F R E) :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] [TopologicalSpace R] =>
    moduleTopology R (TensorProduct F R E)

noncomputable def d18 : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] →
            [inst_4 : Algebra F R] →
              (σ : E →ₐ[F] E) →
                {M : ℕ} →
                  (J : Matrix (Fin M) (Fin M) E) →
                    [TopologicalSpace R] → Set (HA R σ J) → Prop :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] σ {M} J [TopologicalSpace R] s =>
    letI : TopologicalSpace (TensorProduct F R E) := topTens R
    ∃ t, IsOpen t ∧ Subtype.val ⁻¹' t = s

theorem blockM_one_partner_eq_one : ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] (R : Type) [inst_3 : CommRing R] [inst_4 : Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R], d18 R σ J Set.univ := by
  intro F E _ _ _ R _ _ σ M J _
  letI : TopologicalSpace (TensorProduct F R E) := topTens R
  exact ⟨Set.univ, isOpen_univ, rfl⟩

theorem blockM_mul_alt : ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] (R : Type) [inst_3 : CommRing R] [inst_4 : Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R] (s t : Set (HA R σ J)),
  d18 R σ J s →
    d18 R σ J t → d18 R σ J (s ∩ t) := by
  intro F E _ _ _ R _ _ σ M J _ s t hs ht
  letI : TopologicalSpace (TensorProduct F R E) := topTens R
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := ht
  exact ⟨a ∩ b, ha.inter hb, rfl⟩

theorem conj_invariant_character_mem : ∀ {F E : Type} [inst : Field F]
  [inst_1 : Field E] [inst_2 : Algebra F E] (R : Type) [inst_3 : CommRing R] [inst_4 : Algebra F R] (σ : E →ₐ[F] E)
  {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R]
  (s : Set (Set (HA R σ J))),
  (∀ t ∈ s, d18 R σ J t) → d18 R σ J (⋃₀ s) := by
  intro F E _ _ _ R _ _ σ M J _ s hs
  letI : TopologicalSpace (TensorProduct F R E) := topTens R
  refine ⟨⋃₀ {u : Set (Matrix.GeneralLinearGroup (Fin M) (TensorProduct F R E)) |
    IsOpen u ∧ Subtype.val ⁻¹' u ∈ s}, isOpen_sUnion (fun u hu => hu.1), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_sUnion]
  constructor
  · rintro ⟨u, ⟨_, hu⟩, hx⟩
    exact ⟨_, hu, hx⟩
  · rintro ⟨t, ht, hx⟩
    obtain ⟨u, hu, rfl⟩ := hs t ht
    exact ⟨u, ⟨hu, ht⟩, hx⟩

@[reducible] noncomputable def instTopologicalSpaceHA : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] →
            [inst_4 : Algebra F R] →
              (σ : E →ₐ[F] E) →
                {M : ℕ} →
                  (J : Matrix (Fin M) (Fin M) E) →
                    [TopologicalSpace R] → TopologicalSpace (HA R σ J) :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] σ {M} J [TopologicalSpace R] =>
    { IsOpen := d18 R σ J,
      isOpen_univ := blockM_one_partner_eq_one R σ J,
      isOpen_inter := blockM_mul_alt R σ J,
      isOpen_sUnion := conj_invariant_character_mem R σ J }

attribute [local instance] instTopologicalSpaceHA

private theorem closed_UJ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ)
    (J : Matrix n n A) :
    IsClosed ((UJ σ J : Subgroup (Matrix.GeneralLinearGroup n A)) :
      Set (Matrix.GeneralLinearGroup n A)) := by
  have hv : Continuous (fun g : Matrix.GeneralLinearGroup n A => (g : Matrix n n A)) :=
    Units.continuous_val
  have hc : Continuous (fun g : Matrix.GeneralLinearGroup n A =>
      cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) := by
    simp only [cT]
    exact ((hv.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hv
  exact isClosed_eq hc continuous_const

private theorem lcsc_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] {n : Type} [Fintype n]
    [DecidableEq n] :
    LocallyCompactSpace (Matrix.GeneralLinearGroup n A) ∧
      SecondCountableTopology (Matrix.GeneralLinearGroup n A) ∧
      T2Space (Matrix.GeneralLinearGroup n A) := by
  haveI : LocallyCompactSpace (Matrix n n A) := inferInstanceAs (LocallyCompactSpace (n → n → A))
  haveI : SecondCountableTopology (Matrix n n A) :=
    inferInstanceAs (SecondCountableTopology (n → n → A))
  haveI : SecondCountableTopology (Matrix n n A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have he : Topology.IsClosedEmbedding (Units.embedProduct (Matrix n n A)) :=
    Units.isClosedEmbedding_embedProduct
  exact ⟨he.locallyCompactSpace, he.isEmbedding.secondCountableTopology, he.isEmbedding.t2Space⟩

private theorem lcsc_sub {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    LocallyCompactSpace H ∧ SecondCountableTopology H ∧ T2Space H :=
  ⟨hH.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology, inferInstance⟩

private theorem props_of_free {R D : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [Ring D] [Algebra R D]
    {ι : Type} [Fintype ι] (B : Module.Basis ι R D) [Module.Finite R D] [TopologicalSpace D]
    [IsModuleTopology R D] :
    IsTopologicalRing D ∧ LocallyCompactSpace D ∧ SecondCountableTopology D ∧ T2Space D := by
  have hr := IsModuleTopology.isTopologicalRing R D
  haveI := IsModuleTopology.toContinuousAdd R D
  let e := B.equivFun
  have c1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have c2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : D ≃ₜ (ι → R) := { toEquiv := e.toEquiv, continuous_toFun := c1, continuous_invFun := c2 }
  exact ⟨hr, h.isClosedEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology,
    h.isEmbedding.t2Space⟩

private theorem sigR_continuous {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [TopologicalSpace (TensorProduct F R E)]
    [IsModuleTopology R (TensorProduct F R E)] (σ : E →ₐ[F] E) :
    Continuous (sigR R σ) := by
  haveI := IsModuleTopology.toContinuousAdd R (TensorProduct F R E)
  have h : (⇑(sigR R σ) : TensorProduct F R E → TensorProduct F R E) =
      ⇑(LinearMap.baseChange R σ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add a b ha hb => simp [map_add (f := _), ha, hb]
  rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

theorem lcsc_HA : ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] [FiniteDimensional F E] (R : Type) [inst_4 : CommRing R] [inst_5 : Algebra F R]
  [inst_6 : TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
  LocallyCompactSpace (HA R σ J) ∧
    SecondCountableTopology (HA R σ J) ∧
      T2Space (HA R σ J) := by
  intro F E _ _ _ _ R _ _ _ _ _ _ _ σ M J
  letI τ : TopologicalSpace (TensorProduct F R E) := topTens R
  haveI hm : IsModuleTopology R (TensorProduct F R E) := ⟨rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ :=
    props_of_free (Algebra.TensorProduct.basis R (Module.finBasis F E))
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g1, g2, g3⟩ := lcsc_GL (A := TensorProduct F R E) (n := Fin M)
  haveI := g1
  haveI := g2
  haveI := g3
  have hc := closed_UJ (sigR R σ) (sigR_continuous R σ) (JR R J)
  exact lcsc_sub _ hc

end UpperTheory.Reformulated.B.Yzd4
