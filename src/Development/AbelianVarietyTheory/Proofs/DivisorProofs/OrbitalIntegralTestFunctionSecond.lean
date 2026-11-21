import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import GroundTheory.Brauer.BaseChangeCSA
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchMu
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrbitCentralizerAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCentralizerTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugacyClassClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointOfEventuallyIntegralLocaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactIntegralUnitaryPointsAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultLabelRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCentralizerOfCommutePadicPointsSpli
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelFiniteClassNumberCentraliserTorus
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialZeroLocusCoordinates

section
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem isOpen_of_padicLattice {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V] [TopologicalSpace V] [IsModuleTopology ℚ_[p] V]
    (A : AddSubgroup V) (hA : ∀ c : ℚ_[p], ‖c‖ ≤ 1 → ∀ v ∈ A, c • v ∈ A)
    (hN : ∀ v : V, ∃ N : ℕ, (p : ℚ_[p]) ^ N • v ∈ A) : IsOpen (A : Set V) := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[p] V
  let b := Module.finBasis ℚ_[p] V
  choose N hN' using fun i => hN (b i)
  set M := ∑ i, N i with hMdef
  have hp1 : ‖(p : ℚ_[p])‖ ≤ 1 := Padic.norm_p_lt_one.le
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hb : ∀ i, (p : ℚ_[p]) ^ M • b i ∈ A := by
    intro i
    have hle : N i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact hA _ (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1) _ (hN' i)
  have hpos : 0 < ‖(p : ℚ_[p]) ^ M‖ := norm_pos_iff.2 (pow_ne_zero _ hp0)
  let U : Set V := ⋂ i, (fun v => b.coord i v) ⁻¹' Metric.closedBall 0 ‖(p : ℚ_[p]) ^ M‖
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => ?_
    exact (IsUltrametricDist.isOpen_closedBall _ hpos.ne').preimage
      (IsModuleTopology.continuous_of_linearMap (b.coord i))
  have hUA : U ⊆ A := by
    intro v hv
    simp only [U, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hv
    rw [← b.sum_repr v]
    refine A.sum_mem fun i _ => ?_
    have : b.repr v i • b i = (b.repr v i / (p : ℚ_[p]) ^ M) • ((p : ℚ_[p]) ^ M • b i) := by
      rw [smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hp0)]
    rw [this]
    refine hA _ ?_ _ (hb i)
    rw [norm_div, div_le_one hpos]
    exact hv i
  have h0 : (0 : V) ∈ U := by
    simp [U, hpos.le]
  exact AddSubgroup.isOpen_of_mem_nhds A (Filter.mem_of_superset (hU.mem_nhds h0) hUA)

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem exists_pow_smul_norm_le_one (z : PadicAlgCl p) : ∃ N : ℕ, ‖(p : ℚ_[p]) ^ N • z‖ ≤ 1 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hz') (Padic.norm_p_lt_one (p := p))
  refine ⟨N, ?_⟩
  rw [Algebra.smul_def, norm_mul, map_pow, norm_pow, PadicAlgCl.norm_extends]
  calc ‖(p : ℚ_[p])‖ ^ N * ‖z‖ ≤ ‖z‖⁻¹ * ‖z‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ hz'.ne'

theorem algebraMap_mem_intKQ (r : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) :
    algebraMap ℚ_[p] (KQ p K r) c ∈ intKQ p K r := by
  have hK : algebraMap ℚ_[p] K c ∈ GlobalTheory.LKLoc.intK p K := by
    show algebraMap K (PadicAlgCl p) (algebraMap ℚ_[p] K c) ∈ Obar p
    rw [← IsScalarTower.algebraMap_apply, mem_Obar_iff]
    exact (PadicAlgCl.norm_extends (p := p) c).le.trans hc
  exact Subring.subset_closure (Or.inl ⟨⟨_, hK⟩, rfl⟩)

theorem smul_mem_intKQ (r : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) (v : KQ p K r) (hv : v ∈ intKQ p K r) :
    c • v ∈ intKQ p K r := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem_intKQ p K r c hc) hv

theorem exists_pow_smul_mem_intKQ (r : ℕ) (v : KQ p K r) :
    ∃ N : ℕ, (p : ℚ_[p]) ^ N • v ∈ intKQ p K r := by
  have hp1 : ∀ k : ℕ, ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le
  induction (v : K ⊗[ℚ_[p]] Qr p r) using TensorProduct.induction_on with
  | zero => exact ⟨0, by show (p : ℚ_[p]) ^ 0 • (0 : KQ p K r) ∈ intKQ p K r; rw [smul_zero]; exact zero_mem _⟩
  | tmul x y =>
    obtain ⟨N₁, h₁⟩ := exists_pow_smul_norm_le_one p (x : PadicAlgCl p)
    obtain ⟨N₂, h₂⟩ := exists_pow_smul_norm_le_one p (y : PadicAlgCl p)
    have hx : (p : ℚ_[p]) ^ N₁ • x ∈ GlobalTheory.LKLoc.intK p K := by
      show (((p : ℚ_[p]) ^ N₁ • x : K) : PadicAlgCl p) ∈ Obar p
      rw [IntermediateField.coe_smul, mem_Obar_iff]; exact h₁
    have hy : (p : ℚ_[p]) ^ N₂ • y ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
      show (((p : ℚ_[p]) ^ N₂ • y : Qr p r) : PadicAlgCl p) ∈ Obar p
      rw [IntermediateField.coe_smul, mem_Obar_iff]; exact h₂
    refine ⟨N₁ + N₂, ?_⟩
    have key : ((p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y) : K ⊗[ℚ_[p]] Qr p r) =
        (((p : ℚ_[p]) ^ N₁ • x) ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] ((p : ℚ_[p]) ^ N₂ • y)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul_smul, pow_add]
    have e : (p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y : KQ p K r) =
        inclK p K r ((p : ℚ_[p]) ^ N₁ • x) * inclQ p K r ((p : ℚ_[p]) ^ N₂ • y) := key
    show (p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y : KQ p K r) ∈ intKQ p K r
    rw [e]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, hx⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, hy⟩, rfl⟩))
  | add a b ha hb =>
    obtain ⟨N₁, h₁⟩ := ha
    obtain ⟨N₂, h₂⟩ := hb
    refine ⟨N₁ + N₂, ?_⟩
    have e : (p : ℚ_[p]) ^ (N₁ + N₂) • (a + b) =
        (p : ℚ_[p]) ^ N₂ • ((p : ℚ_[p]) ^ N₁ • a) + (p : ℚ_[p]) ^ N₁ • ((p : ℚ_[p]) ^ N₂ • b) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm N₂ N₁]
    show (p : ℚ_[p]) ^ (N₁ + N₂) • (a + b : KQ p K r) ∈ intKQ p K r
    rw [e]
    exact add_mem (smul_mem_intKQ p K r _ (hp1 _) _ h₁) (smul_mem_intKQ p K r _ (hp1 _) _ h₂)

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isOpen_intKQ (hK : FiniteDimensional ℚ_[p] K) (r : ℕ) (hr : 0 < r) :
    IsOpen (intKQ p K r : Set (KQ p K r)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI : FiniteDimensional ℚ_[p] (KQ p K r) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  exact isOpen_of_padicLattice (intKQ p K r).toAddSubgroup
    (fun c hc v hv => smul_mem_intKQ p K r c hc v hv) (exists_pow_smul_mem_intKQ p K r)

theorem mem_Kres_iff (n r : ℕ) (g : GL (Fin n) (KQ p K r)) :
    g ∈ Kres p K n r ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r ∧
      ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r := by
  constructor
  · rintro ⟨h, rfl⟩ i j
    exact ⟨((h : Matrix (Fin n) (Fin n) (intKQ p K r)) i j).2,
      (((h⁻¹ : GL (Fin n) (intKQ p K r)) : Matrix (Fin n) (Fin n) (intKQ p K r)) i j).2⟩
  · intro H
    let A : Matrix (Fin n) (Fin n) (intKQ p K r) := Matrix.of fun i j => ⟨_, (H i j).1⟩
    let B : Matrix (Fin n) (Fin n) (intKQ p K r) := Matrix.of fun i j => ⟨_, (H i j).2⟩
    have hA : A.map (intKQ p K r).subtype = (g : Matrix (Fin n) (Fin n) (KQ p K r)) := by ext i j; rfl
    have hB : B.map (intKQ p K r).subtype =
        ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) := by ext i j; rfl
    have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) (intKQ p K r) => M.map (intKQ p K r).subtype :=
      Matrix.map_injective Subtype.val_injective
    have h1 : A * B = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
      exact Units.mul_inv g)
    have h2 : B * A = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
      exact Units.inv_mul g)
    exact ⟨⟨A, B, h1, h2⟩, Units.ext hA⟩

theorem isOpen_Kres : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → IsOpen (Kres p K n r : Set (GL (Fin n) (KQ p K r))) := by
  intro p _ K hK n r hr
  have hS := isOpen_intKQ p K hK r hr
  have e : (Kres p K n r : Set (GL (Fin n) (KQ p K r))) = ⋂ i, ⋂ j,
      ((fun g : GL (Fin n) (KQ p K r) => (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) ⁻¹' (intKQ p K r : Set _) ∩
       (fun g : GL (Fin n) (KQ p K r) =>
          ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j) ⁻¹' (intKQ p K r : Set _)) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    exact mem_Kres_iff p K n r g
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (hS.preimage (Units.continuous_val.matrix_elem i j)).inter
    (hS.preimage (Units.continuous_coe_inv.matrix_elem i j))

end GlobalTheory.LKRes
end
end

section
open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKMid

theorem t2Space_kq {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    T2Space (KQ p K r) := by
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  let b := Module.Free.chooseBasis ℚ_[p] (KQ p K r)
  let φ : KQ p K r →ₗ[ℚ_[p]] (Module.Free.ChooseBasisIndex ℚ_[p] (KQ p K r) → ℚ_[p]) :=
    Finsupp.lcoeFun ∘ₗ b.repr.toLinearMap
  have hinj : Function.Injective φ := by
    intro x y h
    apply b.repr.injective
    exact DFunLike.coe_injective h
  exact T2Space.of_injective_continuous hinj (IsModuleTopology.continuous_of_linearMap φ)

end GlobalTheory.LKMid
end
end

section
open Matrix GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.BCFL
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.IntBasisKQ
open ReciprocityTheory.DiscreteGroups.LocalClassField

variable (p : ℕ) [Fact p.Prime]

theorem exists_basis_OK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    ∃ (ι : Type) (_ : Fintype ι) (β : Module.Basis ι ℚ_[p] K),
      ∀ x : K, x ∈ OK p K ↔ ∀ i, ‖β.repr x i‖ ≤ 1 := by
  letI := zpAlgOK p K
  haveI := isScalarTower_zp_OK p K
  haveI := isIntegralClosure_OK p K
  haveI := isTorsionFree_zp_K p K
  haveI : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  haveI : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (OK p K) (nonZeroDivisors ℤ_[p])) K :=
    IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] K (OK p K)
  let β₀ := Module.finBasis ℤ_[p] (OK p K)
  let β := β₀.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) K
  refine ⟨_, inferInstance, β, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · have e : x = algebraMap (OK p K) K ⟨x, hx⟩ := rfl
    rw [e, Module.Basis.localizationLocalization_repr_algebraMap]
    exact (β₀.repr ⟨x, hx⟩ i).2
  · let z : _ → ℤ_[p] := fun i => ⟨β.repr x i, hx i⟩
    have hx' : x = algebraMap (OK p K) K (∑ i, z i • β₀ i) := by
      conv_lhs => rw [← β.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply ℤ_[p] (OK p K) K,
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, ← Module.Basis.localizationLocalization_apply ℚ_[p]
        (nonZeroDivisors ℤ_[p]) K]
      rfl
    rw [hx']
    exact (∑ i, z i • β₀ i).2

end GlobalTheory.IntBasisKQ

namespace GlobalTheory.IntBasisKQ

variable (p : ℕ) [Fact p.Prime]

section Tensor

variable {A B : Type} [CommRing A] [Algebra ℚ_[p] A] [CommRing B] [Algebra ℚ_[p] B]
  {ι κ : Type} [Fintype ι] [Fintype κ] (β : Module.Basis ι ℚ_[p] A) (γ : Module.Basis κ ℚ_[p] B)
  (OA : Subring A) (OB : Subring B)

def IntCoord (z : A ⊗[ℚ_[p]] B) : Prop := ∀ k, ‖(β.tensorProduct γ).repr z k‖ ≤ 1

variable {p β γ}

theorem intCoord_add {z w : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) (hw : IntCoord p β γ w) :
    IntCoord p β γ (z + w) := fun k => by
  rw [map_add, Finsupp.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz k) (hw k))

theorem intCoord_smul {z : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    IntCoord p β γ (c • z) := fun k => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hz k)

theorem intCoord_neg {z : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) : IntCoord p β γ (-z) := fun k => by
  rw [map_neg, Finsupp.neg_apply, norm_neg]
  exact hz k

theorem intCoord_zero : IntCoord p β γ (0 : A ⊗[ℚ_[p]] B) := fun k => by simp

theorem intCoord_sum {σ : Type} (s : Finset σ) (f : σ → A ⊗[ℚ_[p]] B) (h : ∀ t ∈ s, IntCoord p β γ (f t)) :
    IntCoord p β γ (∑ t ∈ s, f t) := by
  induction s using Finset.induction_on with
  | empty => simpa using intCoord_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intCoord_add (h a (Finset.mem_insert_self _ _)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

variable {OA OB}

theorem intCoord_tmul (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    {a : A} {b : B} (ha : a ∈ OA) (hb : b ∈ OB) : IntCoord p β γ (a ⊗ₜ[ℚ_[p]] b) := fun ⟨i, j⟩ => by
  rw [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ((hB b).1 hb j) (norm_nonneg _) ((hA a).1 ha i)

theorem basis_mem (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (i : ι) : β i ∈ OA :=
  (hA _).2 fun i' => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem intCoord_mul (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    {z w : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) (hw : IntCoord p β γ w) : IntCoord p β γ (z * w) := by
  set b := β.tensorProduct γ
  have e : z * w = ∑ k, ∑ l, (b.repr z k * b.repr w l) • (b k * b l) := by
    conv_lhs => rw [← b.sum_repr z, ← b.sum_repr w]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm]
  rw [e]
  refine intCoord_sum _ _ fun k _ => intCoord_sum _ _ fun l _ => intCoord_smul ?_ ?_
  · obtain ⟨i, j⟩ := k
    obtain ⟨i', j'⟩ := l
    simp only [b, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.tmul_mul_tmul]
    exact intCoord_tmul hA hB (OA.mul_mem (basis_mem hA i) (basis_mem hA i'))
      (OB.mul_mem (basis_mem hB j) (basis_mem hB j'))
  · rw [norm_mul]
    exact mul_le_one₀ (hz k) (norm_nonneg _) (hw l)

theorem mem_closure_iff (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    (z : A ⊗[ℚ_[p]] B) :
    z ∈ Subring.closure (Set.range (fun a : OA => (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) a) ∪
      Set.range (fun b : OB => (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) b)) ↔
      ∀ k, ‖(β.tensorProduct γ).repr z k‖ ≤ 1 := by
  let S : Subring (A ⊗[ℚ_[p]] B) :=
    { carrier := {z | IntCoord p β γ z}
      mul_mem' := intCoord_mul hA hB
      one_mem' := intCoord_tmul hA hB OA.one_mem OB.one_mem
      add_mem' := intCoord_add
      zero_mem' := intCoord_zero
      neg_mem' := intCoord_neg }
  constructor
  · intro hz
    refine (Subring.closure_le (t := S)).2 (Set.union_subset ?_ ?_) hz
    · rintro _ ⟨a, rfl⟩
      exact intCoord_tmul hA hB a.2 OB.one_mem
    · rintro _ ⟨b, rfl⟩
      exact intCoord_tmul hA hB OA.one_mem b.2
  · intro hz
    rw [← (β.tensorProduct γ).sum_repr z]
    refine Subring.sum_mem _ fun ⟨i, j⟩ _ => ?_
    rw [Module.Basis.tensorProduct_apply, TensorProduct.smul_tmul',
      show ((β.tensorProduct γ).repr z (i, j) • β i) ⊗ₜ[ℚ_[p]] γ j =
        (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) ((β.tensorProduct γ).repr z (i, j) • β i) *
        (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) (γ j) by
          rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨_, ?_⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, basis_mem hB j⟩, rfl⟩))
    refine (hA _).2 fun i' => ?_
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, norm_mul]
    refine mul_le_one₀ (hz (i, j)) (norm_nonneg _) ?_
    split_ifs <;> simp

end Tensor

end GlobalTheory.IntBasisKQ

namespace GlobalTheory.IntBasisKQ

theorem exists_basis_intKQ : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℚ_[p] (KQ p K r)),
      ∀ x, x ∈ intKQ p K r ↔ ∀ i, ‖b.repr x i‖ ≤ 1 := by
  intro p _ K hK r hr
  obtain ⟨ι₁, _, β, hβ⟩ := exists_basis_OK p K hK
  obtain ⟨ι₂, _, γ, hγ⟩ := exists_basis_OK p (Qr p r)
    (ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr)
  refine ⟨ι₁ × ι₂, inferInstance, β.tensorProduct γ, fun x => ?_⟩
  exact mem_closure_iff (OA := GlobalTheory.LKLoc.intK p K) (OB := GlobalTheory.LKLoc.intR p (Q0 p) r) hβ hγ x

end GlobalTheory.IntBasisKQ
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

open scoped Pointwise

namespace GlobalTheory.FinAtP

variable {p : ℕ} [Fact p.Prime]

theorem kq_lc (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    LocallyCompactSpace (KQ p K 1) ∧ SecondCountableTopology (KQ p K 1) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : ContinuousSMul ℚ_[p] (KQ p K 1) := IsModuleTopology.toContinuousSMul ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  let b := Module.finBasis ℚ_[p] (KQ p K 1)
  let e : KQ p K 1 ≃L[ℚ_[p]] (Fin (Module.finrank ℚ_[p] (KQ p K 1)) → ℚ_[p]) :=
    b.equivFun.toContinuousLinearEquiv
  exact ⟨e.toHomeomorph.isClosedEmbedding.locallyCompactSpace,
    e.toHomeomorph.isEmbedding.secondCountableTopology⟩

theorem isCompact_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    IsCompact (intKQ p K 1 : Set (KQ p K 1)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : ContinuousSMul ℚ_[p] (KQ p K 1) := IsModuleTopology.toContinuousSMul ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  obtain ⟨ι, _, b, hb⟩ := GlobalTheory.IntBasisKQ.exists_basis_intKQ p K inferInstance 1 one_pos
  let e : KQ p K 1 ≃L[ℚ_[p]] (ι → ℚ_[p]) := b.equivFun.toContinuousLinearEquiv
  have hset : (intKQ p K 1 : Set (KQ p K 1)) = e ⁻¹' Set.univ.pi fun _ => Metric.closedBall (0 : ℚ_[p]) 1 := by
    ext x
    simp only [SetLike.mem_coe, hb, Set.mem_preimage, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
    rfl
  rw [hset]
  exact e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ => isCompact_closedBall _ _)

theorem isCompact_Kres (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (n : ℕ) :
    IsCompact (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  set B : Set (Matrix (Fin n) (Fin n) (KQ p K 1)) := {M | ∀ i j, M i j ∈ intKQ p K 1} with hB
  have hBc : IsCompact B := by
    have : B = Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (intKQ p K 1 : Set (KQ p K 1)) := by
      ext M
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_intKQ K
  have hB' : IsCompact (MulOpposite.unop ⁻¹' B : Set (Matrix (Fin n) (Fin n) (KQ p K 1))ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hBc
  have e : (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))) = Units.embedProduct _ ⁻¹' (B ×ˢ (MulOpposite.unop ⁻¹' B)) := by
    ext g
    simp only [SetLike.mem_coe, mem_Kres_iff, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
      MulOpposite.unop_op, hB, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hBc.prod hB')

open Polynomial in

theorem rho_charpoly_sep (G : HTGroup p) (w : Fin G.m) (y : G.C) (hdeg : (minpoly G.F y).natDegree = G.n)
    (hsep : (minpoly G.F y).Separable) : (G.rho w y).charpoly.Separable := by
  letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  let ρF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    { G.rho w with
      commutes' := fun x => by
        change G.rho w (algebraMap G.F G.C x) = _
        rw [G.rho_F]
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
          RingHom.algebraMap_toAlgebra, HTGroup.embW] }
  have hρF : ∀ c, ρF c = G.rho w c := fun _ => rfl
  let Φ : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) ρF (fun _ _ => Algebra.commute_algebraMap_left _ _)
  have hΦinj : Function.Injective Φ :=
    (Φ : G.Fw w ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) (G.Fw w)).injective
  set z : G.Fw w ⊗[G.F] G.C := (1 : G.Fw w) ⊗ₜ y with hz
  have hΦz : Φ z = G.rho w y := by
    change Φ ((1 : G.Fw w) ⊗ₜ y) = _
    refine (Algebra.TensorProduct.lift_tmul (Algebra.ofId (G.Fw w) (Matrix (Fin G.n) (Fin G.n) (G.Fw w))) ρF _
      (1 : G.Fw w) y).trans ?_
    rw [map_one, one_mul]
    exact hρF y
  set M := G.rho w y with hM
  have hliF : LinearIndependent G.F (fun i : Fin G.n => y ^ (i : ℕ)) := by
    have h := linearIndependent_pow (K := G.F) y
    rw [hdeg] at h
    exact h
  have hliC : LinearIndependent (G.Fw w) (fun i : Fin G.n => z ^ (i : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := G.Fw w) hliF
    convert h using 1
    funext i
    simp [z, Algebra.TensorProduct.tmul_pow]
  have hMint : IsIntegral (G.Fw w) M := Algebra.IsIntegral.isIntegral M
  have hQ0 : minpoly (G.Fw w) M ≠ 0 := minpoly.ne_zero hMint
  have hzQ : aeval z (minpoly (G.Fw w) M) = 0 := by
    apply hΦinj
    rw [map_zero, ← Polynomial.aeval_algHom_apply, hΦz, minpoly.aeval]
  have hdegQ : G.n ≤ (minpoly (G.Fw w) M).natDegree := by
    by_contra hlt
    push_neg at hlt
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at hzQ
    have hc := Fintype.linearIndependent_iff.1 hliC (fun i => (minpoly (G.Fw w) M).coeff i) hzQ
    apply hQ0
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_zero]
    by_cases hk : k < G.n
    · exact hc ⟨k, hk⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  set Pv := (minpoly G.F y).map (algebraMap G.F (G.Fw w)) with hPv
  have hPvM : aeval M Pv = 0 := by
    rw [hPv, Polynomial.aeval_map_algebraMap, hM, ← hρF, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hyint : IsIntegral G.F y := Algebra.IsIntegral.isIntegral y
  have hPvmon : Pv.Monic := (minpoly.monic hyint).map _
  have hPvdeg : Pv.natDegree = G.n := by
    rw [hPv, Polynomial.natDegree_map, hdeg]
  have hdvd : minpoly (G.Fw w) M ∣ Pv := minpoly.dvd (G.Fw w) M hPvM
  have hmin : minpoly (G.Fw w) M = Pv :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hMint) hPvmon hdvd (by omega)).symm
  have hchar : M.charpoly = Pv := by
    have h1 : minpoly (G.Fw w) M ∣ M.charpoly := Matrix.minpoly_dvd_charpoly M
    have h2 : M.charpoly.natDegree = G.n := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    rw [hmin] at h1
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPvmon (Matrix.charpoly_monic M) h1
      (by omega)
  rw [hchar, hPv]
  exact hsep.map

theorem loc (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {n : ℕ}
    (γ : GL (Fin n) (KQ p K 1)) (hγ : (γ : Matrix (Fin n) (Fin n) (KQ p K 1)).charpoly.Separable)
    (S₂ : Finset (GL (Fin n) (KQ p K 1))) :
    ∃ S : Finset (GL (Fin n) (KQ p K 1)), ∀ h : GL (Fin n) (KQ p K 1),
      (∃ s ∈ S₂, ∃ k₁ ∈ Kres p K n 1, ∃ k₂ ∈ Kres p K n 1, h⁻¹ * γ * h = k₁ * s * k₂) →
      ∃ a : GL (Fin n) (KQ p K 1), a * γ = γ * a ∧ ∃ s ∈ S, ∃ k ∈ Kres p K n 1, h = a * s * k := by
  obtain ⟨hlc, hsc⟩ := kq_lc K
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  haveI : IsArtinianRing (KQ p K 1) := IsArtinianRing.of_finite ℚ_[p] (KQ p K 1)
  have hK := isCompact_Kres K n
  have hO := isOpen_Kres p K inferInstance n 1 one_pos
  set Ω : Set (GL (Fin n) (KQ p K 1)) := ⋃ s ∈ S₂,
    (fun x : GL (Fin n) (KQ p K 1) × GL (Fin n) (KQ p K 1) => x.1 * s * x.2) ''
      ((Kres p K n 1 : Set _) ×ˢ (Kres p K n 1 : Set _)) with hΩdef
  have hΩ : IsCompact Ω := S₂.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop)
  obtain ⟨C, hC, hCx⟩ := GlobalTheory.Orb.isProperOrbit_GL (A := KQ p K 1) (g := γ) hγ Ω hΩ
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun c : C => (c : GL (Fin n) (KQ p K 1)) • (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))))
    (fun c => hO.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, Set.mem_smul_set.2 ⟨1, one_mem _, by simp⟩⟩)
  refine ⟨t.image fun c : C => (c : GL (Fin n) (KQ p K 1)), fun h ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩ => ?_⟩
  have hmem : h⁻¹ * γ * h ∈ Ω := Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, he.symm⟩
  obtain ⟨u, hu, huC⟩ := hCx h hmem
  have := ht huC
  simp only [Set.mem_iUnion] at this
  obtain ⟨c, hc, hx⟩ := this
  obtain ⟨k, hk, hck⟩ := Set.mem_smul_set.1 hx
  refine ⟨u⁻¹, ?_, c, Finset.mem_image_of_mem _ hc, k, hk, ?_⟩
  · have hu' : u * γ = γ * u := GlobalTheory.Orb.mem_cent.1 hu
    calc u⁻¹ * γ = u⁻¹ * (γ * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * γ) * u⁻¹ := by rw [hu']
      _ = γ * u⁻¹ := by group
  · have e : u * h = (c : GL (Fin n) (KQ p K 1)) * k := hck.symm
    calc h = u⁻¹ * (u * h) := by group
      _ = u⁻¹ * c * k := by rw [e]; group

end GlobalTheory.FinAtP

namespace GlobalTheory.FinAtP

variable {p : ℕ} [Fact p.Prime]

theorem gl_one_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem prod_fin (G : HTGroup p) (γ : Gr G 1)
    (hγ : ∀ w, ((γ.2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).charpoly.Separable)
    (S₂ : Finset (Gr G 1)) :
    ∃ S : Finset (Gr G 1), ∀ h : Gr G 1,
      (∃ s ∈ S₂, ∃ k₁ ∈ KHT p G.m G.n 1 G.Fw, ∃ k₂ ∈ KHT p G.m G.n 1 G.Fw, h⁻¹ * γ * h = k₁ * s * k₂) →
      ∃ a : Gr G 1, a * γ = γ * a ∧ ∃ s ∈ S, ∃ k ∈ KHT p G.m G.n 1 G.Fw, h = a * s * k := by
  choose Sw hSw using fun w => loc (G.Fw w) (γ.2 w) (hγ w) (S₂.image fun s => s.2 w)
  refine ⟨(Fintype.piFinset Sw).image fun t => ((1 : GL (Fin 1) (Qr p 1)), t), ?_⟩
  rintro h ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩
  have hw : ∀ w, ∃ a : GL (Fin G.n) (KQ p (G.Fw w) 1), a * γ.2 w = γ.2 w * a ∧
      ∃ s ∈ Sw w, ∃ k ∈ Kres p (G.Fw w) G.n 1, h.2 w = a * s * k := fun w =>
    hSw w (h.2 w) ⟨s.2 w, Finset.mem_image_of_mem _ hs, k₁.2 w, (Subgroup.mem_prod.1 hk₁).2 w (Set.mem_univ _),
      k₂.2 w, (Subgroup.mem_prod.1 hk₂).2 w (Set.mem_univ _), congrArg (fun x : Gr G 1 => x.2 w) he⟩
  choose a ha s' hs' k hk hk' using hw
  refine ⟨(h.1, a), Prod.ext (gl_one_comm _ _) (funext ha), (1, s'),
    Finset.mem_image.2 ⟨s', Fintype.mem_piFinset.2 hs', rfl⟩, (1, k),
    Subgroup.mem_prod.2 ⟨one_mem _, fun w _ => hk w⟩, Prod.ext (by simp) (funext fun w => ?_)⟩
  simp [hk' w]

theorem exists_finset_cosets {H : Type} [Group H] (K₀ K : Subgroup H) (hK : K.relIndex K₀ ≠ 0) :
    ∃ T : Finset H, ∀ k ∈ K₀, ∃ t ∈ T, ∃ k' ∈ K, k = t * k' := by
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hK⟩
  haveI : Finite (K₀ ⧸ K.subgroupOf K₀) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K₀ ⧸ K.subgroupOf K₀) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : H), fun k hk => ?_⟩
  set q : K₀ ⧸ K.subgroupOf K₀ := QuotientGroup.mk ⟨k, hk⟩
  have hq : (Quotient.out q)⁻¹ * (⟨k, hk⟩ : K₀) ∈ K.subgroupOf K₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  rw [Subgroup.mem_subgroupOf] at hq
  refine ⟨((Quotient.out q : K₀) : H), Finset.mem_image_of_mem _ (Finset.mem_univ _), _, hq, ?_⟩
  simp

theorem charpoly_formGroupToPadicPoints_component (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (w : Fin G.m) :
    (((toP1 G β y).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).charpoly =
      (G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).charpoly.map (inclK p (G.Fw w) 1).toRingHom := by
  rw [← Matrix.charpoly_map]
  rfl

end GlobalTheory.FinAtP
end
end

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.LocFinIrr

def conjMA (H : Type*) [Group H] : MulAction H H where
  smul g y := g * y * g⁻¹
  one_smul y := by show 1 * y * 1⁻¹ = y; group
  mul_smul a b y := by show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹; group

theorem conjMA_cont (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    @ContinuousSMul H H (conjMA H).toSMul _ _ :=
  @ContinuousSMul.mk H H (conjMA H).toSMul _ _ (by
    show Continuous fun q : H × H => q.1 * q.2 * q.1⁻¹
    fun_prop)

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.OrbFinAf.LocFinIrr
end
end

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.AwayIrr

variable {p : ℕ} [Fact p.Prime]

abbrev xV (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) (v : AwayP p) : (Qv v ⊗[ℚ] G.C)ˣ :=
  Units.map (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom.toMonoidHom x

abbrev yV (G : HTGroup p) (y : G.Cˣ) (v : AwayP p) : (Qv v ⊗[ℚ] G.C)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).toMonoidHom y

theorem piV_toAfF_fst (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (v : AwayP p) :
    ((piV G v (toAfF G β x t hx y) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) =
      xV G x v * yV G (y : G.Cˣ × ℚˣ).1 v * (xV G x v)⁻¹ := by
  apply Units.ext
  set φ := Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) with hφ
  have h0 : (((piV G v (toAfF G β x t hx y) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) :
      Qv v ⊗[ℚ] G.C) = φ ((x : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
        ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := rfl
  rw [h0, map_mul, map_mul]
  simp [φ, Algebra.TensorProduct.map_tmul]

theorem comm_of_comm (G : HTGroup p) (y : G.C) (hdeg : (minpoly G.F y).natDegree = G.n)
    (hsep : (minpoly G.F y).Separable) (v : AwayP p) (X : (Qv v ⊗[ℚ] G.C)ˣ) (a b : Qv v ⊗[ℚ] G.C)
    (ha : a * ((X : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] y) * ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) =
      ((X : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] y) * ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) * a)
    (hb : b * ((X : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] y) * ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) =
      ((X : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] y) * ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) * b) :
    a * b = b * a := by
  have hcsa := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y hsep hdeg
  have hcent : ∀ z : G.C, z * y = y * z ↔
      z ∈ Set.range ((Algebra.adjoin G.F ({y} : Set G.C)).val.restrictScalars ℚ) := by
    intro z
    constructor
    · intro h
      have hz : z ∈ Subalgebra.centralizer G.F {y} := by
        rw [Subalgebra.mem_centralizer_iff]
        simpa using h.symm
      rw [hcsa] at hz
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      have hw : (w : G.C) ∈ Subalgebra.centralizer G.F {y} := by rw [hcsa]; exact w.2
      rw [Subalgebra.mem_centralizer_iff] at hw
      exact (hw _ rfl).symm
  set Xv : Qv v ⊗[ℚ] G.C := (X : Qv v ⊗[ℚ] G.C)
  set Y : Qv v ⊗[ℚ] G.C := ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)
  set g : Qv v ⊗[ℚ] G.C := (1 : Qv v) ⊗ₜ[ℚ] y
  have hXY : Xv * Y = 1 := X.mul_inv
  have hYX : Y * Xv = 1 := X.inv_mul
  have conj : ∀ c : Qv v ⊗[ℚ] G.C, c * (Xv * g * Y) = (Xv * g * Y) * c → (Y * c * Xv) * g = g * (Y * c * Xv) := by
    intro c hc
    calc (Y * c * Xv) * g = Y * c * Xv * g * (Y * Xv) := by rw [hYX, mul_one]
      _ = Y * (c * (Xv * g * Y)) * Xv := by noncomm_ring
      _ = Y * ((Xv * g * Y) * c) * Xv := by rw [hc]
      _ = (Y * Xv) * g * (Y * c * Xv) := by noncomm_ring
      _ = g * (Y * c * Xv) := by rw [hYX, one_mul]
  have hc := GlobalTheory.LKCentAf.commute_of_centralizer ℚ (Qv v) G.C _ y _ hcent _ _ (conj a ha) (conj b hb)
  calc a * b = (Xv * Y) * a * (Xv * Y) * b * (Xv * Y) := by rw [hXY, one_mul, mul_one, mul_one]
    _ = Xv * ((Y * a * Xv) * (Y * b * Xv)) * Y := by noncomm_ring
    _ = Xv * ((Y * b * Xv) * (Y * a * Xv)) * Y := by rw [hc]
    _ = (Xv * Y) * b * (Xv * Y) * a * (Xv * Y) := by noncomm_ring
    _ = b * a := by rw [hXY, one_mul, mul_one, mul_one]

end GlobalTheory.OrbFinAf.AwayIrr

namespace GlobalTheory.OrbFinAf.AwayIrr

variable {p : ℕ} [Fact p.Prime]

theorem isClosed_conjClass' (G : HTGroup p) (v : AwayP p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (X : (Qv v ⊗[ℚ] G.C)ˣ) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    IsClosed {z : (Qv v ⊗[ℚ] G.C)ˣ | ∃ g : (Qv v ⊗[ℚ] G.C)ˣ, z = g * (X * yV G y v * X⁻¹) * g⁻¹} := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  have he₀ : ((yV G y v : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = (1 : Qv v) ⊗ₜ[ℚ] (y : G.C) := rfl
  have hset : {z : (Qv v ⊗[ℚ] G.C)ˣ | ∃ g : (Qv v ⊗[ℚ] G.C)ˣ, z = g * (X * yV G y v * X⁻¹) * g⁻¹} =
      {z : (Qv v ⊗[ℚ] G.C)ˣ | ∃ g : (Qv v ⊗[ℚ] G.C)ˣ, z = g * yV G y v * g⁻¹} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g * X, by group⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g * X⁻¹, by group⟩
  rw [hset]
  exact GlobalTheory.ClosedClass.isClosed_conjClass (Qv v) G.F G.C G.n G.rankC (y : G.C) hsep hdeg (yV G y v) he₀

theorem orbA' (G : HTGroup p) (v : AwayP p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (X : (Qv v ⊗[ℚ] G.C)ˣ) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    ∀ Ω : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact Ω → ∃ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K ∧
      ∀ g : (Qv v ⊗[ℚ] G.C)ˣ, g⁻¹ * (X * yV G y v * X⁻¹) * g ∈ Ω →
        ∃ z : (Qv v ⊗[ℚ] G.C)ˣ, z * (X * yV G y v * X⁻¹) = (X * yV G y v * X⁻¹) * z ∧ ∃ k ∈ K, g = z * k := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) (Qv v ⊗[ℚ] G.C)
  intro Ω hΩ
  obtain ⟨h2, hlc, hsc⟩ := GlobalTheory.T.local_units_locally_compact p G v
  set e := X * yV G y v * X⁻¹ with he
  let act : MulAction (Qv v ⊗[ℚ] G.C)ˣ (Qv v ⊗[ℚ] G.C)ˣ := GlobalTheory.OrbFinAf.LocFinIrr.conjMA _
  have hcs := GlobalTheory.OrbFinAf.LocFinIrr.conjMA_cont (Qv v ⊗[ℚ] G.C)ˣ
  have horb : @MulAction.orbit _ _ act.toSMul e =
      {z : (Qv v ⊗[ℚ] G.C)ˣ | ∃ g : (Qv v ⊗[ℚ] G.C)ˣ, z = g * e * g⁻¹} := by
    ext z; constructor
    · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
  have hcl : IsClosed (@MulAction.orbit _ _ act.toSMul e) := by
    rw [horb]; exact isClosed_conjClass' G v y hdeg hsep X
  obtain ⟨C, hC, hCg⟩ := @GlobalTheory.OrbitSumInt.exists_compact_reach _ _ _ _ _ hlc hsc act _ h2
    (by haveI := h2; infer_instance) hcs e hcl Ω hΩ
  refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
  obtain ⟨c, hc, hce⟩ := hCg g⁻¹ (by show g⁻¹ * e * g⁻¹⁻¹ ∈ Ω; rwa [inv_inv])
  change c * e * c⁻¹ = g⁻¹ * e * g⁻¹⁻¹ at hce
  refine ⟨g * c, ?_, c⁻¹, by simpa using hc, by group⟩
  have : e = g * (c * e * c⁻¹) * g⁻¹ := by rw [hce]; group
  calc g * c * e = g * (c * e * c⁻¹) * c := by group
    _ = g * (c * e * c⁻¹) * g⁻¹ * (g * c) := by group
    _ = e * (g * c) := by rw [← this]

end GlobalTheory.OrbFinAf.AwayIrr

namespace GlobalTheory.OrbFinAf.AwayIrr

open GlobalTheory.OrbFinAf.TorusNorm

variable {p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 2000000 in

theorem normProper (G : HTGroup p) (v : AwayP p) (g0 : Gv G v)
    (hcomA0 : ∀ a b : Qv v ⊗[ℚ] G.C,
      a * (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * a →
      b * (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * b → a * b = b * a) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K → ∃ K' : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K' ∧
      ∀ z : (Qv v ⊗[ℚ] G.C)ˣ, z * ((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1) = ((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1) * z →
      ∀ (s : (Qv v)ˣ), ∀ k ∈ K, (z : Qv v ⊗[ℚ] G.C) * ((k : Qv v ⊗[ℚ] G.C) *
        (starT G.star (Qv v) (k : Qv v ⊗[ℚ] G.C)).unop) * (starT G.star (Qv v) (z : Qv v ⊗[ℚ] G.C)).unop =
        algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (s : Qv v) →
      ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) g0, ∃ m ∈ K', z = (c : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 * m := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  intro K hK
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : ContinuousSMul (Qv v) (Qv v ⊗[ℚ] G.C) := IsModuleTopology.toContinuousSMul (Qv v) _
  have hT2 : T2Space (Qv v ⊗[ℚ] G.C)ˣ := (topA p G v).1
  have hLC : LocallyCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := (topA p G v).2.1
  have hSC : SigmaCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := (topA p G v).2.2
  haveI := locCpt_Qv v
  haveI := secCount_Qv v
  have hS := units_topA (Qv v) (Qv v)
  haveI : T2Space (Qv v)ˣ := hS.1
  haveI : LocallyCompactSpace (Qv v)ˣ := hS.2.1
  haveI : SigmaCompactSpace (Qv v)ˣ := hS.2.2
  set e : (Qv v ⊗[ℚ] G.C)ˣ := (g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 with he_def
  have hsa : ∀ r : Qv v, (starT G.star (Qv v) (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r := by
    intro r
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
      MulOpposite.unop_one]
  let sl : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
    { toFun := fun a => (starT G.star (Qv v) a).unop
      map_add' := fun a b => by simp
      map_smul' := fun r a => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, MulOpposite.unop_mul]
        rw [hsa r]; exact (Algebra.commutes r _).symm }
  have hsl : ∀ a, sl a = (starT G.star (Qv v) a).unop := fun a => rfl
  have hslc : Continuous sl := IsModuleTopology.continuous_of_linearMap sl
  have hsl_mul : ∀ a b, sl (a * b) = sl b * sl a := fun a b => by simp [hsl]
  have hsl1 : sl 1 = 1 := by simp [hsl]
  have hslsl : ∀ a, sl (sl a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => rw [hsl, hsl, starT_tmul, starT_tmul, G.star_star]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  let stU : (Qv v ⊗[ℚ] G.C)ˣ → (Qv v ⊗[ℚ] G.C)ˣ := fun g =>
    ⟨sl g, sl ((g⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C), by rw [← hsl_mul, Units.inv_mul, hsl1],
      by rw [← hsl_mul, Units.mul_inv, hsl1]⟩
  have hstU : ∀ g, ((stU g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = sl g := fun g => rfl
  have hstUc : Continuous stU :=
    Units.continuous_iff.2 ⟨hslc.comp Units.continuous_val, hslc.comp Units.continuous_coe_inv⟩
  have he : ((e : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * sl e =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) ((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : Qv v) := g0.2
  let ι₀ : (Qv v)ˣ →* (Qv v ⊗[ℚ] G.C)ˣ := Units.map (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).toMonoidHom
  have hι₀ : ∀ a, ((ι₀ a : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) a :=
    fun a => rfl
  have hcent : ∀ (a : (Qv v)ˣ) (y : (Qv v ⊗[ℚ] G.C)ˣ), ι₀ a * y = y * ι₀ a :=
    fun a y => Units.ext (Algebra.commutes _ _)
  have hcomA : ∀ a b : Qv v ⊗[ℚ] G.C, a * e = e * a → b * e = e * b → a * b = b * a := hcomA0
  have hsle : ∀ a : Qv v ⊗[ℚ] G.C, a * e = e * a → sl a * e = e * sl a := by
    intro a ha
    have h1 : sl e * sl a = sl a * sl e := by rw [← hsl_mul, ha, hsl_mul]
    have hinv : sl (e : Qv v ⊗[ℚ] G.C) * sl ((e⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = 1 := by
      rw [← hsl_mul, Units.inv_mul, hsl1]
    have key : sl a * e * sl e = e * sl a * sl e := by
      rw [mul_assoc, he, mul_assoc, ← h1, ← mul_assoc, he]
      exact (Algebra.commutes _ _).symm
    calc sl a * e = sl a * e * (sl e * sl ((e⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) := by rw [hinv, mul_one]
      _ = sl a * e * sl e * sl ((e⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by rw [← mul_assoc]
      _ = e * sl a * sl e * sl ((e⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by rw [key]
      _ = e * sl a := by rw [mul_assoc (e * sl a), hinv, mul_one]
  have hslm : ∀ a b : Qv v ⊗[ℚ] G.C, a * e = e * a → b * e = e * b → sl (a * b) = sl a * sl b :=
    fun a b ha hb => by rw [hsl_mul]; exact hcomA _ _ (hsle b hb) (hsle a ha)
  obtain ⟨W, hW, hWs⟩ := GlobalTheory.T.exists_sqrt_fixed_near_one_commutative_centralizer p v (Qv v ⊗[ℚ] G.C) (e : Qv v ⊗[ℚ] G.C) sl hcomA hsle hslm hsl1
  let Z : Subgroup (Qv v ⊗[ℚ] G.C)ˣ := Subgroup.centralizer {e}
  have hZ : ∀ z : (Qv v ⊗[ℚ] G.C)ˣ, z ∈ Z ↔ (z : Qv v ⊗[ℚ] G.C) * e = e * z := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff, Units.ext_iff, Units.val_mul, Units.val_mul]
  have hZc : IsClosed (Z : Set (Qv v ⊗[ℚ] G.C)ˣ) := by
    have : (Z : Set (Qv v ⊗[ℚ] G.C)ˣ) = {z | z * e = e * z} := by
      ext z; exact Subgroup.mem_centralizer_singleton_iff
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  haveI : LocallyCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  have hcommZ : ∀ a b : Z, a * b = b * a := fun a b => Subtype.ext (Units.ext
    (hcomA _ _ ((hZ _).1 a.2) ((hZ _).1 b.2)))
  let τ : Z →* Z :=
    { toFun := fun z => ⟨stU z.1, (hZ _).2 (hsle _ ((hZ _).1 z.2))⟩
      map_one' := Subtype.ext (Units.ext hsl1)
      map_mul' := fun a b => Subtype.ext (Units.ext (hslm _ _ ((hZ _).1 a.2) ((hZ _).1 b.2))) }
  have hτ : ∀ z : Z, (((τ z : Z) : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = sl ((z : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) :=
    fun z => rfl
  have hτc : Continuous τ := continuous_induced_rng.2 (hstUc.comp continuous_subtype_val)
  have hτi : ∀ z, τ (τ z) = z := fun z => Subtype.ext (Units.ext (hslsl _))
  have hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s := by
    refine ⟨(fun z : Z => ((z : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) ⁻¹' W,
      (Units.continuous_val.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (by simpa using hW), ?_⟩
    intro s hs hτs
    have hss : sl ((s : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = ((s : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) :=
      congrArg (fun u : Z => ((u : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) hτs
    obtain ⟨r, hre, hrs, hrr⟩ := hWs _ hs ((hZ _).1 s.2) hss
    have hrr2 : r * r = ((s : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := hrr
    set sA : (Qv v ⊗[ℚ] G.C)ˣ := (s : (Qv v ⊗[ℚ] G.C)ˣ) with hsA
    have hrsc : r * sA = sA * r := by rw [← hrr2]; exact (mul_assoc r r r).symm
    have hrs' : ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * r = r * ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
      calc ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * r
          = ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * r * (sA * ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) := by
            rw [Units.mul_inv, mul_one]
        _ = ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * (r * sA) * ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
            simp only [mul_assoc]
        _ = ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * (sA * r) * ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
            rw [hrsc]
        _ = r * ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    let ru : (Qv v ⊗[ℚ] G.C)ˣ := ⟨r, ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * r,
      by rw [hrs', ← mul_assoc, hrr2, Units.mul_inv], by rw [mul_assoc, hrr2, Units.inv_mul]⟩
    refine ⟨⟨ru, (hZ ru).2 hre⟩, Subtype.ext (Units.ext hrs), Subtype.ext (Units.ext hrr2)⟩
  let ι : (Qv v)ˣ →* Z :=
    { toFun := fun a => ⟨ι₀ a, (hZ _).2 (Algebra.commutes _ _)⟩
      map_one' := Subtype.ext (map_one ι₀)
      map_mul' := fun a b => Subtype.ext (map_mul ι₀ a b) }
  have hιc : Continuous ι := continuous_induced_rng.2
    (Continuous.units_map (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).toMonoidHom (continuous_algebraMap (Qv v) _))
  have hτι : ∀ a, τ (ι a) = ι a := fun a => Subtype.ext (Units.ext (hsa (a : Qv v)))
  have hU : ∃ U ∈ nhds (1 : (Qv v)ˣ), ∀ a ∈ U, a * a = 1 → a = 1 := by
    have h1 : (1 : (Qv v)ˣ) ≠ -1 := by
      intro h
      have h' := congrArg (fun u : (Qv v)ˣ => (u : Qv v)) h
      simp only [Units.val_one, Units.val_neg] at h'
      haveI : CharZero (Qv v) := charZero_of_injective_algebraMap (algebraMap ℚ (Qv v)).injective
      have h2 : (2 : Qv v) = 0 := by linear_combination h'
      exact two_ne_zero h2
    refine ⟨{a | a ≠ -1}, isOpen_ne.mem_nhds h1, fun a ha haa => ?_⟩
    have h2 : (a : Qv v) * a = 1 := by rw [← Units.val_mul, haa, Units.val_one]
    rcases mul_self_eq_one_iff.1 h2 with h3 | h3
    · exact Units.ext h3
    · exact absurd (Units.ext (by rw [h3, Units.val_neg, Units.val_one])) ha
  let D : Set Z := (fun z : Z => (z : (Qv v ⊗[ℚ] G.C)ˣ)) ⁻¹' ((fun k : (Qv v ⊗[ℚ] G.C)ˣ => (k * stU k)⁻¹) '' K)
  have hD : IsCompact D := hZc.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hK.image ((continuous_id.mul hstUc).inv))
  obtain ⟨B, hB, hBs⟩ := exists_compact_mod_sim Z (Qv v)ˣ hcommZ (fun a b => mul_comm a b) τ hτc hτi hsq ι hιc
    hτι hU D hD
  refine ⟨(fun b : Z => (b : (Qv v ⊗[ℚ] G.C)ˣ)) '' B, hB.image continuous_subtype_val, ?_⟩
  intro z hze s k hk hzk
  have hzZ : z ∈ Z := Subgroup.mem_centralizer_singleton_iff.2 hze
  have hU' : z * (k * stU k) * stU z = ι₀ s := Units.ext hzk
  have hD' : τ ⟨z, hzZ⟩ * ⟨z, hzZ⟩ * (ι s)⁻¹ ∈ D := by
    refine ⟨k, hk, ?_⟩
    show (k * stU k)⁻¹ = stU z * z * (ι₀ s)⁻¹
    have h1 : k * stU k = z⁻¹ * ι₀ s * (stU z)⁻¹ := by rw [← hU']; group
    rw [h1, ← map_inv ι₀ s]
    simp only [_root_.mul_inv_rev, inv_inv, ← map_inv ι₀ s, mul_assoc]
    rw [hcent]
  obtain ⟨u, l, hul, b, hb, hzub⟩ := hBs ⟨z, hzZ⟩ s hD'
  rw [hcommZ] at hul
  refine ⟨⟨((u : (Qv v ⊗[ℚ] G.C)ˣ), l), congrArg (fun w : Z => ((w : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) hul⟩,
    ?_, (b : (Qv v ⊗[ℚ] G.C)ˣ), ⟨b, hb, rfl⟩, congrArg Subtype.val hzub⟩
  show _ * g0 = g0 * _
  exact Subtype.ext (Prod.ext (Subgroup.mem_centralizer_singleton_iff.1 u.2) (mul_comm _ _))

end GlobalTheory.OrbFinAf.AwayIrr

namespace GlobalTheory.OrbFinAf.AwayIrr

variable {p : ℕ} [Fact p.Prime]

theorem val_conj (G : HTGroup p) (v : AwayP p) (y : G.Cˣ) (X : (Qv v ⊗[ℚ] G.C)ˣ) :
    ((X * yV G y v * X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
      (X : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] (y : G.C)) * ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
  rw [Units.val_mul, Units.val_mul]; rfl

theorem local_fin' (G : HTGroup p) (v : AwayP p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (X : (Qv v ⊗[ℚ] G.C)ˣ) (g0 : Gv G v)
    (hg0 : ((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) = X * yV G y v * X⁻¹)
    (Ω : Set (Gv G v)) (hΩ : IsCompact Ω) : ∃ D : Set (Gv G v), IsCompact D ∧ ∀ g : Gv G v,
      g⁻¹ * g0 * g ∈ Ω → ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) g0, ∃ d ∈ D, g = c * d := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) (Qv v ⊗[ℚ] G.C)
  have hcomA : ∀ a b : Qv v ⊗[ℚ] G.C,
      a * (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * a →
      b * (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * b → a * b = b * a := by
    intro a b ha hb
    rw [hg0, val_conj] at ha hb
    exact comm_of_comm G (y : G.C) hdeg hsep v X a b ha hb
  have hcont : Continuous fun d : Gv G v => (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 :=
    continuous_fst.comp continuous_subtype_val
  obtain ⟨K, hK, hKg⟩ := orbA' G v y hdeg hsep X _ (hΩ.image hcont)
  obtain ⟨K', hK', hK'g⟩ := normProper G v g0 hcomA K hK
  set K'' : Set (Qv v ⊗[ℚ] G.C)ˣ := (fun q : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v ⊗[ℚ] G.C)ˣ => q.1 * q.2) '' (K' ×ˢ K)
  have hK'' : IsCompact K'' := (hK'.prod hK).image continuous_mul
  refine ⟨{d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K''}, GlobalTheory.T.isCompact_unitaryPointsAtPlace_fst_mem_compact p G v K'' hK'', ?_⟩
  intro g hg
  have h1 : (g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1⁻¹ * (X * yV G y v * X⁻¹) *
      (g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ (fun d : Gv G v => (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1) '' Ω := by
    rw [← hg0]; exact ⟨_, hg, rfl⟩
  obtain ⟨z, hz, k, hk, hgz⟩ := hKg _ h1
  rw [← hg0] at hz
  have hgm : (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
      (starT G.star (Qv v) (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := g.2
  rw [hgz, Units.val_mul, map_mul, MulOpposite.unop_mul] at hgm
  have hgm' : (z : Qv v ⊗[ℚ] G.C) * ((k : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) (k : Qv v ⊗[ℚ] G.C)).unop) *
      (starT G.star (Qv v) (z : Qv v ⊗[ℚ] G.C)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := by
    rw [← hgm]; simp only [mul_assoc]
  obtain ⟨c, hc, m, hm, hzc⟩ := hK'g z hz _ k hk hgm'
  refine ⟨c, hc, c⁻¹ * g, ⟨(m, k), ⟨hm, hk⟩, ?_⟩, by group⟩
  show m * k = ((c : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ * (g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1
  rw [hgz, hzc]; group

end GlobalTheory.OrbFinAf.AwayIrr

namespace GlobalTheory.OrbFinAf.AwayIrr

variable {p : ℕ} [Fact p.Prime]

theorem lattice' (G : HTGroup p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (x : (AfP p ⊗[ℚ] G.C)ˣ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ g : (Qv v ⊗[ℚ] G.C)ˣ,
      IsIntV G v ((g⁻¹ * (xV G x v * yV G y v * (xV G x v)⁻¹) * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) →
      IsIntV G v ((g⁻¹ * (xV G x v * yV G y v * (xV G x v)⁻¹)⁻¹ * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) →
      ∃ e : (Qv v ⊗[ℚ] G.C)ˣ, e * (xV G x v * yV G y v * (xV G x v)⁻¹) =
        (xV G x v * yV G y v * (xV G x v)⁻¹) * e ∧ IsIntV G v ((e⁻¹ * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
        IsIntV G v ((g⁻¹ * e : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
  filter_upwards [GlobalTheory.T.eventually_completedTensor_matrix_split_semilocal p G (y : G.C) hdeg hsep, isIntV_mul_eventually G,
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G (x : AfP p ⊗[ℚ] G.C),
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C),
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G ((1 : AfP p) ⊗ₜ[ℚ] (y : G.C))] with v hA hmul hx1 hx2 hγ1
  intro g h1 _
  obtain ⟨K, _, R, Φ, hfin, hInt, Q, hQs, hQm⟩ := hA
  set xv := xV G x v with hxv
  set γ₀ := yV G y v with hγ₀
  have hγ0 : IsIntV G v (γ₀ : Qv v ⊗[ℚ] G.C) := by
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at hγ1
    exact hγ1
  have e1 : (xv⁻¹ * g)⁻¹ * γ₀ * (xv⁻¹ * g) = g⁻¹ * (xv * γ₀ * xv⁻¹) * g := by group
  obtain ⟨U, hU, hU1, hU2⟩ := GlobalTheory.OrbFinAf.KottLat.conj_integral R Φ hfin Q hQs γ₀ hQm ((hInt _).1 hγ0)
    (xv⁻¹ * g) (by rw [e1]; exact (hInt _).1 h1)
  have hU1' : IsIntV G v (U : Qv v ⊗[ℚ] G.C) := (hInt _).2 hU1
  have hU2' : IsIntV G v ((U⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := (hInt _).2 hU2
  have key : U⁻¹ * γ₀ = ((xv⁻¹ * g)⁻¹ * γ₀ * (xv⁻¹ * g)) * U⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hU, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨g * U⁻¹ * xv⁻¹, ?_, ?_, ?_⟩
  · calc g * U⁻¹ * xv⁻¹ * (xv * γ₀ * xv⁻¹) = g * (U⁻¹ * γ₀) * xv⁻¹ := by group
      _ = g * (((xv⁻¹ * g)⁻¹ * γ₀ * (xv⁻¹ * g)) * U⁻¹) * xv⁻¹ := by rw [key]
      _ = xv * γ₀ * xv⁻¹ * (g * U⁻¹ * xv⁻¹) := by group
  · rw [show (g * U⁻¹ * xv⁻¹)⁻¹ * g = xv * U by group, Units.val_mul]
    exact hmul _ _ hx1 hU1'
  · rw [show g⁻¹ * (g * U⁻¹ * xv⁻¹) = U⁻¹ * xv⁻¹ by group, Units.val_mul]
    exact hmul _ _ hU2' hx2

theorem norm' (G : HTGroup p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (x : (AfP p ⊗[ℚ] G.C)ˣ) (g0 : ∀ v : AwayP p, Gv G v)
    (hg0 : ∀ v, ((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) = xV G x v * yV G y v * (xV G x v)⁻¹) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ s : (Qv v ⊗[ℚ] G.C)ˣ,
      s * (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 = (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 * s →
      IsIntV G v (s : Qv v ⊗[ℚ] G.C) → IsIntV G v ((s⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) →
      (starT G.star (Qv v) s).unop = s →
      ∃ u : (Qv v ⊗[ℚ] G.C)ˣ, u * (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 = (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 * u ∧
        IsIntV G v (u : Qv v ⊗[ℚ] G.C) ∧ IsIntV G v ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
        (u : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) u).unop = s := by
  obtain ⟨δ, hδ⟩ : ∃ δ : G.F, IsCMField.complexConj G.F δ ≠ δ := by
    let τ : G.F →+* ℂ := Classical.arbitrary _
    obtain ⟨y, -, hy⟩ := G.hKq.2 τ
    refine ⟨y, fun h => hy ?_⟩
    have h2 := IsCMField.complexEmbedding_complexConj G.F τ y
    rw [h] at h2
    have h3 := congrArg Complex.im h2
    rw [Complex.conj_im] at h3
    linarith
  have hd0 : δ - IsCMField.complexConj G.F δ ≠ 0 := sub_ne_zero.2 (Ne.symm hδ)
  filter_upwards [GlobalTheory.T.eventually_integral_tensor_points_sharp_stable_ring p G, GlobalTheory.T.eventually_isIntV_one_tmul p G (algebraMap G.F G.C δ),
    GlobalTheory.T.eventually_isIntV_one_tmul p G (algebraMap G.F G.C (δ - IsCMField.complexConj G.F δ)⁻¹),
    GlobalTheory.T.eventually_isIntV_one_tmul p G (algebraMap ℚ G.C (1 / 2))] with v hO h1 h2 h3
  obtain ⟨hO1, hOm, hOs⟩ := hO
  have hmem := (g0 v).2
  have hcomm : ∀ a b : Qv v ⊗[ℚ] G.C,
      a * (((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * a →
      b * (((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * b → a * b = b * a := by
    intro a b ha hb
    rw [hg0, val_conj] at ha hb
    exact comm_of_comm G (y : G.C) hdeg hsep v _ a b ha hb
  have central : ∀ c : G.C, (∀ z : G.C, c * z = z * c) → ∀ w : Qv v ⊗[ℚ] G.C,
      w * ((1 : Qv v) ⊗ₜ[ℚ] c) = ((1 : Qv v) ⊗ₜ[ℚ] c) * w := by
    intro c hc w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r z => simp [Algebra.TensorProduct.tmul_mul_tmul, hc z]
    | add a b ha hb => rw [add_mul, mul_add, ha, hb]
  have cF : ∀ a : G.F, ∀ z : G.C, algebraMap G.F G.C a * z = z * algebraMap G.F G.C a :=
    fun a z => Algebra.commutes a z
  have cQ : ∀ a : ℚ, ∀ z : G.C, algebraMap ℚ G.C a * z = z * algebraMap ℚ G.C a :=
    fun a z => Algebra.commutes a z
  have hstar : (starT G.star (Qv v) ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C δ)).unop =
      (1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (IsCMField.complexConj G.F δ) := by
    rw [starT_tmul, G.star_F]
  have hprod : ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C δ -
      (starT G.star (Qv v) ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C δ)).unop) *
      ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (δ - IsCMField.complexConj G.F δ)⁻¹) = 1 := by
    rw [hstar, ← TensorProduct.tmul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← map_sub,
      ← map_mul, mul_inv_cancel₀ hd0, map_one]
    exact Algebra.TensorProduct.one_def.symm
  have hh : (1 : Qv v) ⊗ₜ[ℚ] algebraMap ℚ G.C (1 / 2) = algebraMap ℚ (Qv v ⊗[ℚ] G.C) (1 / 2) :=
    (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).commutes (1 / 2)
  have h2h : (2 : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] algebraMap ℚ G.C (1 / 2)) = 1 := by
    rw [hh, ← map_ofNat (algebraMap ℚ (Qv v ⊗[ℚ] G.C)) 2, ← map_mul, show (2 : ℚ) * (1 / 2) = 1 by norm_num, map_one]
  exact GlobalTheory.T.integral_order_centralizer_stable p G v _ _ hmem hO1 hOm hOs hcomm _ _ _
    (central _ (cF δ) _).symm (central _ (cF _) _).symm (central _ (cQ _) _).symm h1 h2 h3 hprod h2h

theorem kottwitz_almost' (G : HTGroup p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (x : (AfP p ⊗[ℚ] G.C)ˣ) (g0 : ∀ v : AwayP p, Gv G v)
    (hg0 : ∀ v, ((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) = xV G x v * yV G y v * (xV G x v)⁻¹) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ g : Gv G v, g⁻¹ * g0 v * g ∈ IntV G v →
      ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (g0 v), ∃ d ∈ IntV G v, g = c * d := by
  filter_upwards [GlobalTheory.T.eventually_isIntegralInCompletedTensorBasis_mul_explicit p G, GlobalTheory.T.star_preserves_integrality p G, lattice' G y hdeg hsep x, norm' G y hdeg hsep x g0 hg0]
    with v h1 h2 h3 h4
  intro g hg
  have h3' : ∀ g : (Qv v ⊗[ℚ] G.C)ˣ,
      IsIntV G v ((g⁻¹ * (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) →
      IsIntV G v ((g⁻¹ * ((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) →
      ∃ e : (Qv v ⊗[ℚ] G.C)ˣ, e * (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 = (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 * e ∧
        IsIntV G v ((e⁻¹ * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
        IsIntV G v ((g⁻¹ * e : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
    rw [hg0]; exact h3
  obtain ⟨c, hc, d, hd, hgd⟩ := GlobalTheory.OrbFinAf.KottAlmost.step (K := Qv v) (A := Qv v ⊗[ℚ] G.C)
    (starT G.star (Qv v)) (GlobalTheory.OrbFinAf.KottAlmost.starT_starT G (Qv v)) (IsIntV G v)
    (fun z => z ∈ v.1.adicCompletionIntegers ℚ) (one_mem _) h1 h2 (g0 v) h3' h4 g ⟨hg.1, hg.2.1⟩
  exact ⟨c, hc, d, hd, hgd⟩

end GlobalTheory.OrbFinAf.AwayIrr

namespace GlobalTheory.OrbFinAf.AwayIrr

open scoped Pointwise

end GlobalTheory.OrbFinAf.AwayIrr
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_p_neighborhood_in_level_subgroup : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r₂ : Gr G 1), letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C); ∃ O : Set ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, r₂⁻¹ * psiP G z * r₂ ∈ KHT p G.m G.n 1 G.Fw := by
  first | (exact @GlobalTheory.TorCls.OpenP.openp) | (exact GlobalTheory.TorCls.OpenP.openp) | (intros; apply GlobalTheory.TorCls.OpenP.openp  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls

def TC (D : Type) [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (R : Type) [CommRing R] [Algebra ℚ R]
    (z : (R ⊗[ℚ] D)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] D) * ((1 : R) ⊗ₜ β) * (starT σ R (z.1 : R ⊗[ℚ] D)).unop =
      algebraMap R (R ⊗[ℚ] D) (z.2 : R) * ((1 : R) ⊗ₜ β) ∧
    Commute (z.1 : R ⊗[ℚ] D) ((1 : R) ⊗ₜ y)

end GlobalTheory.CentCls
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls.Fin

theorem classes_finite_of_locus (hloc : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R))) :
    ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u :=
  fun D _ _ _ σ β y p _ => GlobalTheory.TorCls.Borel.classes_finite hloc GlobalTheory.classNumberFinite_holds D σ β y p

theorem classes_finite :
    ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u :=
  classes_finite_of_locus GlobalTheory.TorLoc.exists_locus

end GlobalTheory.CentCls.Fin
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudeCentraliser_classNumber_finite_borel : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u := by
  first | (exact @GlobalTheory.CentCls.Fin.classes_finite) | (exact GlobalTheory.CentCls.Fin.classes_finite) | (intros; apply GlobalTheory.CentCls.Fin.classes_finite  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls

theorem exists_finset_cosets {A : Type} [Group A] (U₀ U : Subgroup A) (h : U.relIndex U₀ ≠ 0) :
    ∃ F : Finset A, ∀ u ∈ U₀, ∃ f ∈ F, f ∈ U₀ ∧ ∃ v ∈ U, u = f * v := by
  haveI : (U.subgroupOf U₀).FiniteIndex := ⟨h⟩
  haveI : Finite (U₀ ⧸ U.subgroupOf U₀) := Subgroup.finite_quotient_of_finiteIndex
  haveI := Fintype.ofFinite (U₀ ⧸ U.subgroupOf U₀)
  refine ⟨Finset.univ.image (fun q : U₀ ⧸ U.subgroupOf U₀ => ((q.out : U₀) : A)), ?_⟩
  intro u hu
  set q : U₀ ⧸ U.subgroupOf U₀ := QuotientGroup.mk ⟨u, hu⟩
  refine ⟨((q.out : U₀) : A), Finset.mem_image_of_mem _ (Finset.mem_univ _), (q.out).2,
    ((q.out : U₀) : A)⁻¹ * u, ?_, by group⟩
  have h1 : (q.out)⁻¹ * ⟨u, hu⟩ ∈ U.subgroupOf U₀ := QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

end GlobalTheory.CentCls

namespace GlobalTheory.CentCls

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → ∀ (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∀ r : G.GAf × Gr G 1, ∃ R : Finset (G.GAf × Gr G 1), ∀ c : G.GAf × Gr G 1, c * (toAfF G β x t hx y₀, toP1 G β y₀) = (toAfF G β x t hx y₀, toP1 G β y₀) * c → ∃ y : grp G β, y * y₀ = y₀ * y ∧ ∃ s ∈ R, ∃ k : G.GAf × Gr G 1, k.1 ∈ L.K.toSubgroup ∧ k.2 ∈ K' ∧ c * r = (toAfF G β x t hx y, toP1 G β y) * s * k := by
  intro p hp G L K' hK' β x t hx hsh y₀ _ _ r
  obtain ⟨r₁, r₂⟩ := r
  obtain ⟨F₂, hF₂⟩ := exists_finset_cosets (KHT p G.m G.n 1 G.Fw) K' hK'.1
  let ι : G.GAf →* (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ :=
    { toFun := fun g => g, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let U₁ : Subgroup ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :=
    ((L.K.toSubgroup.map (MulAut.conj r₁).toMonoidHom).map ι).comap (psiAway G x)
  let U₂ : Subgroup ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ) :=
    ((KHT p G.m G.n 1 G.Fw).map (MulAut.conj r₂).toMonoidHom).comap (psiP G)
  obtain ⟨O₁, hO₁, h1O₁, hO₁K⟩ :=
    exists_open_psiAway_mem_conj_level p G L β x t hx (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) r₁
  obtain ⟨O₂, hO₂, h1O₂, hO₂K⟩ := GlobalTheory.T.psi_p_neighborhood_in_level_subgroup p G r₂
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeCentraliser_classNumber_finite_borel G.C G.star (β : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) p
    (U₁.prod U₂) ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, ⟨h1O₁, h1O₂⟩,
      fun z hz hT1 _ => Subgroup.mem_prod.mpr ⟨by
        obtain ⟨k, hk, hk'⟩ := hO₁K z.1 hz.1 hT1
        exact Subgroup.mem_comap.mpr
          (Subgroup.mem_map.mpr ⟨r₁ * k * r₁⁻¹, Subgroup.mem_map.mpr ⟨k, hk, rfl⟩, hk'⟩), by
        have h2 := hO₂K z.2 hz.2
        refine Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨r₂⁻¹ * psiP G z.2 * r₂, h2, ?_⟩)
        show r₂ * (r₂⁻¹ * psiP G z.2 * r₂) * r₂⁻¹ = psiP G z.2
        group⟩⟩
  let Pf : G.Cˣ × ℚˣ → Prop := fun e =>
    (e.1 : G.C) * β * MulOpposite.unop (G.star e.1) = algebraMap ℚ G.C e.2 * β ∧
      Commute (e.1 : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
  let e₀ : G.Cˣ × ℚˣ := if h : ∃ e, Pf e ∧ (e.2 : ℚ) < 0 then h.choose else 1
  let S' := S ∪ S.image (fun s => dg G.C p e₀ * s)
  let gOf : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ → G.GAf := fun w =>
    if h : ∃ g : G.GAf, (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w then h.choose else 1
  have hgOf : ∀ w (g : G.GAf), (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w →
      ((gOf w : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w := by
    intro w g hg
    have h : ∃ g : G.GAf, (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w := ⟨g, hg⟩
    simp only [gOf, dif_pos h]
    exact h.choose_spec
  refine ⟨(S' ×ˢ F₂).image (fun q => (gOf (psiAway G x q.1.1) * r₁, psiP G q.1.2 * r₂ * q.2)), ?_⟩
  intro c hc
  obtain ⟨c₁, c₂⟩ := c
  have hc1 : c₁ * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c₁ := congrArg Prod.fst hc
  have hc2 : c₂ * toP1 G β y₀ = toP1 G β y₀ * c₂ := congrArg Prod.snd hc
  have hz₁ := inT_psiAway_inv_of_commute p G β x t hx y₀ c₁ hc1
  obtain ⟨z₂, hz₂, hz₂c⟩ := GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split p G β hsh y₀ c₂ hc2
  obtain ⟨γ, hγf, hγc, s, hs, u, hu, hz⟩ := hS (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), z₂) hz₁ hz₂
  obtain ⟨γ', ⟨hγ'f, hγ'c⟩, hγ'pos, s', hs', hds⟩ : ∃ γ' : G.Cˣ × ℚˣ, Pf γ' ∧ (0 : ℚ) < (γ'.2 : ℚ) ∧
      ∃ s' ∈ S', dg G.C p γ * s = dg G.C p γ' * s' := by
    rcases lt_or_gt_of_ne (Units.ne_zero γ.2) with hneg | hpos
    · have hex : ∃ e, Pf e ∧ (e.2 : ℚ) < 0 := ⟨γ, ⟨hγf, hγc⟩, hneg⟩
      have he₀ : e₀ = hex.choose := by simp only [e₀, dif_pos hex]
      obtain ⟨⟨he1, he2⟩, he3⟩ := hex.choose_spec
      refine ⟨γ * e₀⁻¹, ⟨?_, ?_⟩, ?_, dg G.C p e₀ * s,
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs), ?_⟩
      · rw [he₀]
        exact form_mul_inv G.star (β : G.C) γ.1 hex.choose.1 γ.2 hex.choose.2 hγf he1
      · rw [he₀]
        show Commute ((γ.1 * hex.choose.1⁻¹ : G.Cˣ) : G.C) _
        rw [Units.val_mul]
        exact hγc.mul_left he2.units_inv_left
      · rw [he₀]
        show (0 : ℚ) < ((γ.2 * hex.choose.2⁻¹ : ℚˣ) : ℚ)
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.mpr he3)
      · rw [map_mul, map_inv]
        group
    · exact ⟨γ, ⟨hγf, hγc⟩, hpos, s, Finset.mem_union_left _ hs, rfl⟩
  let y : grp G β := ⟨γ', hγ'f, hγ'pos⟩
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_prod.mp hu
  obtain ⟨g, hg1, hg⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu1)
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg1
  obtain ⟨k₂, hk₂, hk₂e⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu2)
  obtain ⟨f, hf, -, v, hv, hkv⟩ := hF₂ k₂ hk₂
  have hz' : (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), z₂) = dg G.C p γ' * s' * u := by
    rw [hz, hds]
  have hz1 := congrArg Prod.fst hz'
  have hz2 := congrArg Prod.snd hz'
  simp only [Prod.fst_mul, Prod.snd_mul] at hz1 hz2
  have hc₁ : (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      psiAway G x (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    simp [psiAway_apply, mul_assoc]
  have e1 : psiAway G x (dg G.C p γ').1 = ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :=
    (toAfF_eq_psiAway G β x t hx y).symm
  rw [hz1, map_mul, map_mul, e1, ← hg] at hc₁
  have hs1 : ((gOf (psiAway G x s'.1) : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = psiAway G x s'.1 := by
    refine hgOf _ ((toAfF G β x t hx y)⁻¹ * c₁ * g⁻¹) ?_
    show ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)⁻¹ *
      (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) * (ι g)⁻¹ = _
    rw [hc₁]
    group
  have hc₁' : c₁ = toAfF G β x t hx y * gOf (psiAway G x s'.1) * g := by
    apply Subtype.ext
    show (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) *
      ((gOf (psiAway G x s'.1) : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) * ι g
    rw [hs1]
    exact hc₁
  have e2 : psiP G (dg G.C p γ').2 = toP1 G β y := (formGroupToPadicPointsDegreeOne_eq_unitaryPoints G β y).symm
  have hc₂' : c₂ = toP1 G β y * psiP G s'.2 * (r₂ * k₂ * r₂⁻¹) := by
    rw [← hz₂c, hz2, map_mul, map_mul, e2, ← hk₂e]
    rfl
  have hg' : g = r₁ * k * r₁⁻¹ := hkg.symm
  have hmem : (s', f) ∈ S' ×ˢ F₂ := Finset.mem_product.mpr ⟨hs', hf⟩
  refine ⟨y, Subtype.ext (Prod.ext (Units.ext hγ'c.eq) (mul_comm _ _)), _,
    Finset.mem_image_of_mem _ hmem, (k, v), hk, hv, ?_⟩
  rw [hc₁', hg', hc₂', hkv]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> simp only [Prod.fst_mul, Prod.snd_mul] <;> group

end GlobalTheory.CentCls
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classNumber_centraliserTorus_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → ∀ (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∀ r : G.GAf × Gr G 1, ∃ R : Finset (G.GAf × Gr G 1), ∀ c : G.GAf × Gr G 1, c * (toAfF G β x t hx y₀, toP1 G β y₀) = (toAfF G β x t hx y₀, toP1 G β y₀) * c → ∃ y : grp G β, y * y₀ = y₀ * y ∧ ∃ s ∈ R, ∃ k : G.GAf × Gr G 1, k.1 ∈ L.K.toSubgroup ∧ k.2 ∈ K' ∧ c * r = (toAfF G β x t hx y, toP1 G β y) * s * k := by
  first | (exact @GlobalTheory.CentCls.main) | (exact GlobalTheory.CentCls.main) | (intros; apply GlobalTheory.CentCls.main  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinPtsSep
open scoped Pointwise in
open IsDedekindDomain GlobalTheory.OrbFinAf GlobalTheory.OrbFinAf.AwayIrr in

theorem fin_cosets_away_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∃ R : Finset G.GAf, ∀ h : G.GAf, f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∃ c : G.GAf, c * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c ∧ ∃ r ∈ R, ∃ k ∈ L.K.toSubgroup, h = c * r * k := by
  intro p _ G L f hf β x t hx y₀ hsep0 hdeg
  set y : G.Cˣ := (y₀ : G.Cˣ × ℚˣ).1 with hy
  have hsep : (minpoly G.F (y : G.C)).Separable := hsep0
  set γ := toAfF G β x t hx y₀ with hγ
  have hg0 : ∀ v, ((piV G v γ : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) =
      xV G x v * yV G y v * (xV G x v)⁻¹ := fun v => piV_toAfF_fst G β x t hx y₀ v
  set T := GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) γ with hT
  set K := L.K.toSubgroup with hK
  obtain ⟨S, hSf⟩ := hf.2.2.2
  let Ω : Set G.GAf := ⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((K : Set G.GAf) ×ˢ (K : Set G.GAf))
  have hΩ : IsCompact Ω := S.isCompact_biUnion fun s _ =>
    (L.compact.prod L.compact).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  have hsupp : ∀ g : G.GAf, f g ≠ 0 → g ∈ Ω := by
    intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩ := hSf g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, e.symm⟩
  let Good : Set (AwayP p) := {v | piV G v '' Ω ⊆ IntV G v ∧
    (∀ g : Gv G v, g⁻¹ * piV G v γ * g ∈ IntV G v → ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (piV G v γ),
      ∃ d ∈ IntV G v, g = c * d) ∧ ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v}
  have hGood : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), v ∈ Good := by
    filter_upwards [GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral p G Ω hΩ, kottwitz_almost' G y hdeg hsep x (fun v => piV G v γ) hg0, GlobalTheory.T.eventually_integralUnitaryPointsAtPlace_mul_mem p G]
      with v h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hL1 := fun v : AwayP p => local_fin' G v y hdeg hsep (xV G x v) (piV G v γ) (hg0 v) (piV G v '' Ω)
    (hΩ.image (GlobalTheory.T.continuous_unitaryAdelicComponentAtPlace_explicit p G v))
  choose D₁ hD₁ hD₁g using hL1
  let D' : ∀ v : AwayP p, Set (Gv G v) := fun v => if v ∈ Good then IntV G v else D₁ v
  have hD'c : ∀ v, IsCompact (D' v) := by
    intro v; by_cases hv : v ∈ Good
    · simp only [D', if_pos hv]; exact GlobalTheory.T.isCompact_integralUnitaryPointsAtPlace p G v
    · simp only [D', if_neg hv]; exact hD₁ v
  have hD'i : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D' v ⊆ IntV G v := by
    filter_upwards [hGood] with v hv
    simp only [D', if_pos hv]; exact le_rfl
  have key : ∀ g : G.GAf, g⁻¹ * γ * g ∈ Ω → ∃ c ∈ T, ∃ d ∈ {g : G.GAf | ∀ v, piV G v g ∈ D' v}, g = c * d := by
    intro g hg
    have hloc : ∀ v, ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (piV G v γ), ∃ d ∈ D' v, piV G v g = c * d := by
      intro v
      have hgv : (piV G v g)⁻¹ * piV G v γ * piV G v g ∈ piV G v '' Ω :=
        ⟨_, hg, by simp only [map_mul, map_inv]⟩
      by_cases hv : v ∈ Good
      · obtain ⟨c, hc, d, hd, e⟩ := hv.2.1 _ (hv.1 hgv)
        exact ⟨c, hc, d, by simp only [D', if_pos hv]; exact hd, e⟩
      · obtain ⟨c, hc, d, hd, e⟩ := hD₁g v _ hgv
        exact ⟨c, hc, d, by simp only [D', if_neg hv]; exact hd, e⟩
    choose c hc d hd e using hloc
    have hcint : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), c v ∈ IntV G v := by
      filter_upwards [GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral p G {g} isCompact_singleton, hGood] with v h1 h2
      have hdv : d v ∈ IntV G v := by have := hd v; simp only [D', if_pos h2] at this; exact this
      have ec : c v = piV G v g * (d v)⁻¹ := by rw [e v]; group
      rw [ec]
      exact h2.2.2 _ (h1 ⟨g, rfl, rfl⟩) _ (inv_mem_IntV G v hdv)
    obtain ⟨tt, htt⟩ := GlobalTheory.T.exists_unitaryAdelicPoint_of_eventually_integral_local p G c hcint
    refine ⟨tt, ?_, tt⁻¹ * g, ?_, by group⟩
    · show tt * γ = γ * (MonoidHom.id _) tt
      apply GlobalTheory.T.unitaryAdelicPoint_ext_of_components p G
      intro v
      have h1 : c v * piV G v γ = piV G v γ * (MonoidHom.id _) (c v) := hc v
      simp only [map_mul, htt, MonoidHom.id_apply] at h1 ⊢
      exact h1
    · intro v
      have : piV G v (tt⁻¹ * g) = d v := by rw [map_mul, map_inv, htt, e v]; group
      rw [this]; exact hd v
  set D := {g : G.GAf | ∀ v, piV G v g ∈ D' v}
  have hD : IsCompact D := GlobalTheory.T.isCompact_unitaryAdelic_prod_local_compacts p G D' hD'c hD'i
  obtain ⟨I, hI⟩ := hD.elim_finite_subcover (fun d : G.GAf => d • (K : Set G.GAf))
    (fun d => L.K.isOpen.smul d) (fun d _ => Set.mem_iUnion.2 ⟨d, ⟨1, one_mem _, mul_one d⟩⟩)
  refine ⟨I, fun h hh => ?_⟩
  obtain ⟨c, hc, d, hd, e⟩ := key _ (hsupp _ hh)
  obtain ⟨i, hi, hdi⟩ := Set.mem_iUnion₂.1 (hI hd)
  obtain ⟨k, hk, rfl⟩ := hdi
  refine ⟨c, hc, i, hi, k, hk, ?_⟩
  rw [e]; simp only [smul_eq_mul]; group

end GlobalTheory.FinPtsSep

noncomputable section

namespace GlobalTheory.FinPtsSep

variable {p : ℕ} [Fact p.Prime]

theorem exists_finset_doubleCoset_cover_of_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (y₀ : grp G β),
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ R : Finset (Gr G 1), ∀ h : Gr G 1, f' (h⁻¹ * toP1 G β y₀ * h) ≠ 0 →
      ∃ c : Gr G 1, c * toP1 G β y₀ = toP1 G β y₀ * c ∧ ∃ r ∈ R, ∃ k ∈ K', h = c * r * k := by
  intro p _ G K' f' hT β y₀ hsep hdeg
  obtain ⟨hcomm, -, -, S₀, hS₀⟩ := hT
  obtain ⟨S, hS⟩ := GlobalTheory.FinAtP.prod_fin G (toP1 G β y₀)
    (fun w => by rw [GlobalTheory.FinAtP.charpoly_formGroupToPadicPoints_component]; exact (GlobalTheory.FinAtP.rho_charpoly_sep G w _ hdeg hsep).map) S₀
  obtain ⟨T, hT⟩ := GlobalTheory.FinAtP.exists_finset_cosets (KHT p G.m G.n 1 G.Fw) K' hcomm.1
  refine ⟨(S ×ˢ T).image fun x => x.1 * x.2, fun h hh => ?_⟩
  obtain ⟨a, ha, s, hs, k, hk, rfl⟩ := hS h (hS₀ _ hh)
  obtain ⟨t, ht, k', hk', rfl⟩ := hT k hk
  exact ⟨a, ha, s * t, Finset.mem_image.2 ⟨(s, t), Finset.mem_product.2 ⟨hs, ht⟩, rfl⟩, k', hk', by group⟩

theorem posV_toV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : PosV G v β) :
    0 < (star ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (herm G v β *ᵥ ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1))).re := by
  have hs := GlobalTheory.LKCx.grp_similitude_herm p G v β y
  have e : star ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (herm G v β *ᵥ ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1)) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) * (star z.1 ⬝ᵥ (herm G v β *ᵥ z.1)) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hs, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [e]
  have hpos : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
  rw [show (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) = ((((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ)) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  exact mul_pos (by exact_mod_cast hpos) z.2

def mapPosV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : PosV G v β) : PosV G v β :=
  ⟨(toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1, posV_toV G v β y z⟩

def conjC (G : HTGroup p) (y : G.Cˣ) : G.C ≃ₐ[G.F] G.C where
  toFun x := y * x * ((y⁻¹ : G.Cˣ) : G.C)
  invFun x := ((y⁻¹ : G.Cˣ) : G.C) * x * y
  left_inv x := by simp [_root_.mul_assoc]
  right_inv x := by simp [_root_.mul_assoc]
  map_mul' a b := by simp [_root_.mul_assoc]
  map_add' a b := by simp [mul_add, add_mul]
  commutes' a := by
    show (y : G.C) * algebraMap G.F G.C a * ((y⁻¹ : G.Cˣ) : G.C) = algebraMap G.F G.C a
    rw [← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

theorem minpoly_conjC (G : HTGroup p) (y g : G.Cˣ) :
    minpoly G.F ((y * g * y⁻¹ : G.Cˣ) : G.C) = minpoly G.F (g : G.C) := by
  have := minpoly.algEquiv_eq (conjC G y) (g : G.C)
  rw [← this]
  rfl

theorem fixL_conj (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (g y : grp G β) (z : Fin G.n → ℂ)
    (h : FixL G v β (g * y * g⁻¹) z) : FixL G v β y ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have e : y * g⁻¹ = g⁻¹ * (g * y * g⁻¹) := by group
  calc (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)
      = (toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β (g * y * g⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, e]
    _ = c • ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by rw [hc, Matrix.mulVec_smul]

theorem finite_pts_conj_fixL_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ γ : grp G β, FixL G v β (γ * y₀ * γ⁻¹) (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * (Quot.out q).1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsees hsym htr y₀
  classical
  by_cases hne : ∃ (b : Dat G v β) (γ : grp G β), FixL G v β (γ * y₀ * γ⁻¹) b.2.1 ∧
      f (b.1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * b.1.1) * f' (b.1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * b.1.2) ≠ 0
  swap
  · convert Set.finite_empty
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨γ, h1, h2⟩
    exact hne ⟨_, γ, h1, h2⟩
  obtain ⟨b₀, γ₀, hfix₀, hne₀⟩ := hne
  have hsd : (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
    have h := hsees (γ₀ * y₀ * γ₀⁻¹) b₀.1.1 (left_ne_zero_of_mul hne₀) ⟨b₀.2.1, b₀.2.2, hfix₀⟩
    have e : (((γ₀ * y₀ * γ₀⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) =
        ((γ₀ : G.Cˣ × ℚˣ).1) * ((y₀ : G.Cˣ × ℚˣ).1) * ((γ₀ : G.Cˣ × ℚˣ).1)⁻¹ := by simp
    rw [e, minpoly_conjC] at h
    exact h
  let z₀ : PosV G v β := mapPosV G v β γ₀⁻¹ b₀.2
  have hz₀ : FixL G v β y₀ z₀.1 := fixL_conj G v β γ₀ y₀ _ hfix₀
  obtain ⟨R1, hR1⟩ := fin_cosets_away_sep p G L f hf β x t hx y₀ hsd.2 hsd.1
  obtain ⟨R2, hR2⟩ := exists_finset_doubleCoset_cover_of_separable p G K' f' hf' β y₀ hsd.2 hsd.1
  have h3 := GlobalTheory.T.finite_classNumber_centraliserTorus_separable p G L K' hf'.1 β x t hx hsym y₀ hsd.2 hsd.1
  choose R3 hR3 using h3
  let Fs : Finset (G.GAf × Gr G 1) := (R1 ×ˢ R2).biUnion R3
  refine (Fs.finite_toSet.image (fun s => (Quot.mk _ (s, z₀) : Pts G v β x t hx L.K.toSubgroup K'))).subset ?_
  rintro q ⟨γ, hfix, hne⟩
  have hq : Quot.mk (Same G v β x t hx L.K.toSubgroup K') (Quot.out q) = q := Quot.out_eq q
  generalize Quot.out q = b at hfix hne hq
  have e1 : (toAfF G β x t hx γ⁻¹ * b.1.1)⁻¹ * toAfF G β x t hx y₀ * (toAfF G β x t hx γ⁻¹ * b.1.1) =
      b.1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * b.1.1 := by
    simp only [map_mul, map_inv]; group
  have e2 : (toP1 G β γ⁻¹ * b.1.2)⁻¹ * toP1 G β y₀ * (toP1 G β γ⁻¹ * b.1.2) =
      b.1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * b.1.2 := by
    simp only [map_mul, map_inv]; group
  obtain ⟨c1, hc1, r1, hr1, k1, hk1, hh1⟩ := hR1 _ (by rw [e1]; exact left_ne_zero_of_mul hne)
  obtain ⟨c2, hc2, r2, hr2, k2, hk2, hh2⟩ := hR2 _ (by rw [e2]; exact right_ne_zero_of_mul hne)
  obtain ⟨y, hy, s, hs, k3, hk31, hk32, hcr⟩ := hR3 (r1, r2) (c1, c2) (Prod.ext hc1 hc2)
  have hfix' : FixL G v β y₀ (mapPosV G v β γ⁻¹ b.2).1 := fixL_conj G v β γ y₀ _ hfix
  let w : PosV G v β := mapPosV G v β y⁻¹ (mapPosV G v β γ⁻¹ b.2)
  have hw : FixL G v β y₀ w.1 := by
    have e : y * y₀ * y⁻¹ = y₀ := by rw [hy]; group
    exact fixL_conj G v β y y₀ _ (by rw [e]; exact hfix')
  obtain ⟨c, hc⟩ := GlobalTheory.LKCx.fixL_pos_unique_of_sep p G v hv β hsym htr y₀ hsd.1 hsd.2 z₀.1 w.1 z₀.2 w.2 hz₀ hw
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := w.2
    rw [hc, zero_smul] at h
    simp at h
  have hb2 : b.2.1 = c • ((toV G v β (γ * y) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z₀.1) := by
    rw [← Matrix.mulVec_smul, ← hc]
    show b.2.1 = (toV G v β (γ * y) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β γ⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ b.2.1))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    simp
  have hb1 : b.1 = ((toAfF G β x t hx (γ * y), toP1 G β (γ * y)) : G.GAf × Gr G 1) * s * (k3 * (k1, k2)) := by
    have hh : ((toAfF G β x t hx γ⁻¹ * b.1.1, toP1 G β γ⁻¹ * b.1.2) : G.GAf × Gr G 1) =
        (c1, c2) * (r1, r2) * (k1, k2) := Prod.ext hh1 hh2
    rw [hcr] at hh
    have hb : b.1 = ((toAfF G β x t hx γ, toP1 G β γ) : G.GAf × Gr G 1) *
        ((toAfF G β x t hx γ⁻¹ * b.1.1, toP1 G β γ⁻¹ * b.1.2) : G.GAf × Gr G 1) := by
      ext <;> simp [← mul_assoc]
    rw [hb, hh]
    ext <;> simp [mul_assoc]
  have hsF : s ∈ Fs := Finset.mem_biUnion.2 ⟨(r1, r2), Finset.mem_product.2 ⟨hr1, hr2⟩, hs⟩
  refine ⟨s, hsF, ?_⟩
  rw [← hq]
  exact Quot.sound ⟨γ * y, k3 * (k1, k2), c, mul_mem hk31 hk1, mul_mem hk32 hk2, hc0, hb1, hb2⟩

end GlobalTheory.FinPtsSep
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.orbital_integral_test_function_second : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ γ : grp G β, FixL G v β (γ * y₀ * γ⁻¹) (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * (Quot.out q).1.2) ≠ 0} := by
  first | exact @GlobalTheory.FinPtsSep.finite_pts_conj_fixL_sep | exact GlobalTheory.FinPtsSep.finite_pts_conj_fixL_sep
end
