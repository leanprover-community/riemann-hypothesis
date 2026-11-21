import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankAlgebraicDataSchrodingerModelLeAleph0

section
namespace GlobalTheory.NatMultipleInLattice

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * a) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have h1 := hy a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have e : ((y.natAbs : ℕ) : E) * a = y • a := by
      rw [zsmul_eq_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1
  · have e : ((y.natAbs : ℕ) : E) * a = -(y • a) := by
      rw [zsmul_eq_mul, ← neg_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1.neg

theorem exists_nsmul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (x : Fin n → E) : ∃ D : ℕ, D ≠ 0 ∧ D • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨D, hD, hy⟩ := hy
    obtain ⟨F, hF, hz⟩ := hz
    refine ⟨D * F, mul_ne_zero hD hF, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.toAddSubmonoid.nsmul_mem hy F
    · rw [mul_smul]; exact L.toAddSubmonoid.nsmul_mem hz D
  | smul a y _ hy =>
    obtain ⟨D, hD, hy⟩ := hy
    obtain ⟨m, hm, hi⟩ := exists_nat_mul_integral a
    refine ⟨m * D, mul_ne_zero hm hD, ?_⟩
    have key := L.smul_mem (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) hy
    have : (m * D) • a • y =
        (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y := by
      have h3 : (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y
          = ((m : E) * a) • D • y := rfl
      rw [h3]
      ext i
      simp only [Pi.smul_apply]
      simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]
      ring
    rw [this]; exact key

end GlobalTheory.NatMultipleInLattice
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.AdelicLatticeIntegral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nsmul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E)
    (x : Fin n → E) : ∃ D : ℕ, D ≠ 0 ∧ D • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice
  | exact _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice
  | (apply _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice ..)

theorem exists_nsmul_map_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E)
    (N : (Fin n → E) →ₗ[E] (Fin n → E)) : ∃ D : ℕ, D ≠ 0 ∧ ∀ y ∈ L, D • N y ∈ L := by
  obtain ⟨s, hs⟩ := hL.fg
  choose! D hD hDm using fun g => exists_nsmul_mem L hL (N g)
  refine ⟨∏ g ∈ s, D g, Finset.prod_ne_zero_iff.mpr fun g _ => hD g, ?_⟩
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem D hg
      rw [hk, mul_comm, mul_smul]; exact nsmul_mem (hDm g) k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact L.add_mem hx hy
  | smul r x _ hx =>
      have : N (r • x) = r • N x := N.map_smul_of_tower r x
      rw [this, smul_comm]; exact L.smul_mem r hx

end GlobalTheory.AdelicLatticeIntegral

namespace GlobalTheory.AdelicLatticeIntegral

theorem exists_finset_smul_mulVec_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ w ∉ S₁, ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a →
      GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F → ∀ y ∈ L,
      a • (M *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)} := by
  intro F E _ _ _ _ _ n M L hL
  classical
  let bF := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) bF
  let c : Fin n × Fin n × Fin (Module.finrank F E) → AF F := fun j => B.repr (M j.1 j.2.1) j.2.2
  let Nm : Fin n × Fin n × Fin (Module.finrank F E) → (Fin n → E) →ₗ[E] (Fin n → E) := fun j =>
    (LinearMap.single E (fun _ : Fin n => E) j.1) ∘ₗ (bF j.2.2 • LinearMap.proj j.2.1)
  let incV : (Fin n → E) → (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) := fun y i =>
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)
  have key : ∀ y, (M *ᵥ incV y) = ∑ j, c j • incV (Nm j y) := by
    intro y
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
    rw [Fintype.sum_prod_type]
    symm
    rw [Finset.sum_eq_single r]
    · rw [Fintype.sum_prod_type]
      symm
      refine Finset.sum_congr rfl fun q _ => ?_
      conv_lhs => rw [← B.sum_repr (M r q)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Nm, incV, B, c, Algebra.TensorProduct.basis_apply, smul_mul_assoc, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    · intro p _ hp
      simp [Nm, incV, Pi.single_apply, Ne.symm hp]
    · simp
  choose D hD0 hDL using fun j => exists_nsmul_map_mem L hL (Nm j)
  let c' : Fin n × Fin n × Fin (Module.finrank F E) → AF F :=
    fun j => c j * algebraMap F (AF F) ((D j : F)⁻¹)
  have hfin : ∀ j, {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F |
      ¬ GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F}.Finite :=
    fun j => Filter.eventually_cofinite.mp (GlobalTheory.AlgCountDim.eventually_evFin_integral (c' j))
  refine ⟨(Set.finite_iUnion hfin).toFinset, ?_⟩
  intro w hw a ha hai y hy
  have hc' : ∀ j, GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F := by
    intro j
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).mpr (Set.mem_iUnion.mpr ⟨j, h⟩))
  have hterm : ∀ j, a • (c j • incV (Nm j y)) = (a * c' j) • incV (D j • Nm j y) := by
    intro j
    have h1 : incV (D j • Nm j y) = D j • incV (Nm j y) := by
      funext i; simp [incV]
    rw [h1, ← Nat.cast_smul_eq_nsmul (AF F), smul_smul, smul_smul]
    congr 1
    have h2 : (D j : F) ≠ 0 := Nat.cast_ne_zero.mpr (hD0 j)
    simp only [c', mul_assoc]
    rw [← map_natCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ h2, map_one, mul_one]
  change a • (M *ᵥ incV y) ∈ _
  rw [key, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  rw [hterm j]
  refine AddSubgroup.subset_closure ⟨a * c' j, ?_, ?_, D j • Nm j y, hDL j y hy, rfl⟩
  · intro u hu
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u a, ha u hu, zero_mul]
  · rw [map_mul]; exact mul_mem hai (hc' j)

end GlobalTheory.AdelicLatticeIntegral
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ w ∉ S₁, ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a →
      GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F → ∀ y ∈ L,
      a • (M *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)} := by
  first | exact @GlobalTheory.AdelicLatticeIntegral.exists_finset_smul_mulVec_mem_closure | exact GlobalTheory.AdelicLatticeIntegral.exists_finset_smul_mulVec_mem_closure | (intros; apply GlobalTheory.AdelicLatticeIntegral.exists_finset_smul_mulVec_mem_closure <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.LatStab

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gen_mul_transpose {n d : ℕ} (x : Fin n → E) (y : Fin d → E) (a : AF F)
    (K : Matrix (Fin d) (Fin d) (AE F E)) :
    (a • incM F (Matrix.vecMulVec x y)) * Kᵀ =
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i))
        (a • (K *ᵥ fun i => inclR (F := F) (AF F) (y i))) := by
  ext i j
  simp only [incM, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply,
    Matrix.transpose_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, map_mul, Finset.smul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  ring

theorem vecMulVec_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : Fin n → E) (hx : x ∈ X.L) (u : Fin d → AE F E)
    (hu : u ∈ AddSubgroup.closure {z | ∃ b : AF F, At (evFin F w) b ∧
          evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => inclR (F := F) (AF F) (y' i)}) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u ∈ latAtV X W w := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨b, hb, hbi, y', hy', rfl⟩ := hu
    apply AddSubgroup.subset_closure
    refine ⟨b, hb, hbi, x, hx, y', hy', ?_⟩
    ext i j
    simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, map_mul]
    rw [mul_smul_comm]
  | zero =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [this]; exact zero_mem _
  | add u v _ _ hu hv =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (u + v) =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u +
          Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) v := by
      ext i j; simp [Matrix.vecMulVec_apply, mul_add]
    rw [this]; exact add_mem hu hv
  | neg u _ hu =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (-u) =
        -Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [this]; exact neg_mem hu

theorem mul_transpose_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (K : Matrix (Fin d) (Fin d) (AE F E))
    (hK : ∀ a : AF F, At (evFin F w) a → evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, At (evFin F w) b ∧
          evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => inclR (F := F) (AF F) (y' i)})
    (γ : Matrix (Fin n) (Fin d) (AE F E)) (hγ : γ ∈ latAtV X W w) : γ * Kᵀ ∈ latAtV X W w := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    rw [gen_mul_transpose]
    exact vecMulVec_mem X W w x hx _ (hK a ha hai y hy)
  | zero => simp
  | add u v _ _ hu hv => rw [Matrix.add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [Matrix.neg_mul]; exact neg_mem hu

theorem latAtV_mul_transpose_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (K K' : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), K' * K = 1 →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K' *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    ∀ γ, γ * Kᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w := by
  intro F E _ _ _ _ _ n d X W w K K' hKK hK hK' γ
  constructor
  · intro h
    have h2 := mul_transpose_mem X W w K' hK' _ h
    rwa [Matrix.mul_assoc, ← Matrix.transpose_mul, hKK, Matrix.transpose_one, Matrix.mul_one] at h2
  · exact mul_transpose_mem X W w K hK γ

end GlobalTheory.LatStab
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLattice_mul_transpose_stable_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (K K' : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), K' * K = 1 →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K' *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    ∀ γ, γ * Kᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w := by
  atlas_forward_decl GlobalTheory.LatStab.latAtV_mul_transpose_iff
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
open scoped Classical

noncomputable section
namespace GlobalTheory.FinDecomp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def idem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : AF F := pairA F 0 (singleFin v 1)

theorem af_ext' {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, evFin F u a = evFin F u b) : a = b :=
  Prod.ext h1 (af_ext fun u => h2 u)

theorem fst_idem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : fstA F (idem F v) = 0 := rfl

theorem evFin_idem (v u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : evFin F u (idem F v) = if u = v then 1 else 0 := by
  split_ifs with h
  · subst h; exact evalV_singleFin_self u 1
  · exact evalV_singleFin_ne h 1

theorem idem_mul_self (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : idem F v * idem F v = idem F v :=
  af_ext' (by simp [map_mul, fst_idem]) fun u => by rw [map_mul, evFin_idem]; split_ifs <;> simp

variable (F) in

def idemS (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) : AF F := ∑ v ∈ S, idem F v

theorem fst_idemS (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) : fstA F (idemS F S) = 0 := by
  simp [idemS, map_sum, fst_idem]

theorem evFin_idemS (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : evFin F u (idemS F S) = if u ∈ S then 1 else 0 := by
  simp [idemS, map_sum, evFin_idem, Finset.sum_ite_eq]

theorem idemS_mul_self (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) : idemS F S * idemS F S = idemS F S :=
  af_ext' (by simp [map_mul, fst_idemS]) fun u => by rw [map_mul, evFin_idemS]; split_ifs <;> simp

theorem idem_mul_idemS_of_mem {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)} (h : w ∈ S) : idem F w * idemS F S = idem F w :=
  af_ext' (by simp [map_mul, fst_idemS, fst_idem]) fun u => by
    rw [map_mul, evFin_idemS, evFin_idem]; split_ifs with h1 h2 <;> simp_all

theorem idem_mul_idemS_of_notMem {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)} (h : w ∉ S) : idem F w * idemS F S = 0 :=
  af_ext' (by simp [map_mul, fst_idemS, fst_idem]) fun u => by
    rw [map_mul, evFin_idemS, evFin_idem, map_zero]; split_ifs with h1 h2 <;> simp_all

theorem mul_idem_of_evFin {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {a : AF F} (h : evFin F v a = 0) : a * idem F v = 0 :=
  af_ext' (by simp [map_mul, fst_idem]) fun u => by
    rw [map_mul, evFin_idem, map_zero]; split_ifs with hu
    · subst hu; simpa using h
    · simp

theorem idem_mul_of_at {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {a : AF F} (h : At (evFin F w) a) : idem F w * a = a := by
  have := h (1 - idem F w) (by simp [evFin_idem])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at this
  exact this.symm

end GlobalTheory.FinDecomp
end

noncomputable section
namespace GlobalTheory.FinDecomp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def phi (e : AF F) (M : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) := (1 - e) • 1 + e • M

theorem phi_mul {e : AF F} (he : e * e = e) (M N : Matrix (Fin n) (Fin n) (AE F E)) :
    phi e (M * N) = phi e M * phi e N := by
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  simp only [phi, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    h1, h2, h3, he, zero_smul, add_zero, zero_add]

theorem phi_mul_orth {e f : AF F} (hef : e * f = 0) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    phi e M * phi f M = phi (e + f) M := by
  have hfe : f * e = 0 := by rw [mul_comm, hef]
  have h1 : (1 - f) * (1 - e) = 1 - (e + f) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hfe, sub_zero]; ring
  have h2 : (1 - f) * e = e := by rw [sub_mul, one_mul, hfe, sub_zero]
  have h3 : f * (1 - e) = f := by rw [mul_sub, mul_one, hfe, sub_zero]
  simp only [phi, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    h1, h2, h3, hfe, zero_smul, add_zero, add_smul]
  abel

theorem phi_one (M : Matrix (Fin n) (Fin n) (AE F E)) : phi (1 : AF F) M = M := by simp [phi]

theorem phi_zero (M : Matrix (Fin n) (Fin n) (AE F E)) : phi (0 : AF F) M = 1 := by simp [phi]

theorem phi_sub_one (e : AF F) (M : Matrix (Fin n) (Fin n) (AE F E)) : phi e M - 1 = e • (M - 1) := by
  simp only [phi, sub_smul, one_smul, smul_sub]; abel

theorem smul_phi_compl {a e : AF F} (h : a * e = 0) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    a • phi (1 - e) M = a • M := by
  simp only [phi, smul_add, smul_smul, sub_sub_cancel, h, zero_smul, zero_add, mul_sub, mul_one, sub_zero]

theorem phi_unitary {σ : E →ₐ[F] E} {e : AF F} (he : e * e = e) {J M : Matrix (Fin n) (Fin n) (AE F E)}
    (hM : Mᵀ * J * M.map (cA σ) = J) : (phi e M)ᵀ * J * (phi e M).map (cA σ) = J := by
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have hm : (phi e M).map (cA σ) = (1 - e) • 1 + e • M.map (cA σ) := by
    ext i j
    simp only [phi, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul, Matrix.one_apply]
    split_ifs <;> simp
  have ht : (phi e M)ᵀ = (1 - e) • 1 + e • Mᵀ := by simp [phi, Matrix.transpose_add, Matrix.transpose_smul]
  rw [hm, ht]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    h1, h2, h3, he, zero_smul, add_zero, zero_add, ← Matrix.mul_assoc, hM]
  rw [← add_smul, sub_add_cancel, one_smul]

section Loc

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}

theorem mat_mul (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : UA σ J) = 1 := rfl

theorem mat_mul_inv (g : UA σ J) : mat g * mat g⁻¹ = 1 := Units.mul_inv g.1

theorem mat_inv_mul (g : UA σ J) : mat g⁻¹ * mat g = 1 := Units.inv_mul g.1

theorem ua_ext {g h : UA σ J} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

def loc (e : AF F) (he : e * e = e) (g : UA σ J) : UA σ J :=
  ⟨⟨phi e (mat g), phi e (mat g⁻¹), by rw [← phi_mul he, mat_mul_inv]; simp only [phi]; rw [← add_smul, sub_add_cancel, one_smul],
      by rw [← phi_mul he, mat_inv_mul]; simp only [phi]; rw [← add_smul, sub_add_cancel, one_smul]⟩, phi_unitary he g.2⟩

theorem mat_loc (e : AF F) (he : e * e = e) (g : UA σ J) : mat (loc e he g) = phi e (mat g) := rfl

theorem mat_loc_inv (e : AF F) (he : e * e = e) (g : UA σ J) : mat (loc e he g)⁻¹ = phi e (mat g⁻¹) := rfl

end Loc

end GlobalTheory.FinDecomp
end

noncomputable section
namespace GlobalTheory.FinDecomp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}

theorem idemS_insert {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)} (h : v ∉ S) :
    idemS F (insert v S) = idem F v + idemS F S := Finset.sum_insert h

theorem mat_prod_loc (g : UA σ J) : ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), l.Nodup →
    mat (l.map fun v => loc (idem F v) (idem_mul_self v) g).prod = phi (idemS F l.toFinset) (mat g)
  | [], _ => by simp [idemS, phi_zero, mat_one]
  | v :: t, hl => by
    rw [List.nodup_cons] at hl
    have hv : v ∉ t.toFinset := by simpa using hl.1
    rw [List.map_cons, List.prod_cons, mat_mul, mat_prod_loc g t hl.2, mat_loc, List.toFinset_cons,
      idemS_insert hv, phi_mul_orth (idem_mul_idemS_of_notMem hv)]

theorem exists_prod_local_mul_latStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) = 0) →
    ∀ T₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∃ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F))
      (l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J),
    T₀ ⊆ S ∧ (∀ x ∈ l, x.1 ∈ S ∧ x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F x.1)) ∧
    h = (l.map Prod.snd).prod * k ∧
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  intro F E _ _ _ _ _ σ B a a' G hG h hinf T₀
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h) G.W.L hG.hW.lat
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h⁻¹) G.W.L hG.hW.lat
  set S := T₀ ∪ S₁ ∪ S₂ with hSdef
  have heS : idemS F S * idemS F S = idemS F S := idemS_mul_self S
  have heS' : (1 - idemS F S) * (1 - idemS F S) = 1 - idemS F S := by
    rw [sub_mul, one_mul, mul_sub, mul_one, heS, sub_self, sub_zero]
  have horth : idemS F S * (1 - idemS F S) = 0 := by rw [mul_sub, mul_one, heS, sub_self]
  set k := loc (1 - idemS F S) heS' h with hk
  have hl : ((S.toList.map fun v => (v, loc (idem F v) (idem_mul_self v) h)).map Prod.snd) =
      S.toList.map fun v => loc (idem F v) (idem_mul_self v) h := by
    rw [List.map_map]; rfl
  have hnot : ∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * idemS F S = 0 := by
    intro w hw u hu
    rw [← idem_mul_of_at hu, mul_comm (idem F w), mul_assoc, idem_mul_idemS_of_notMem hw, mul_zero]
  have hgood : ∀ w ∉ S, ∀ (X : ℕ) (Xs : Spc F E X), ∀ γ, γ * (mat k)ᵀ ∈ latAtV Xs G.W w ↔ γ ∈ latAtV Xs G.W w := by
    intro w hw X Xs γ
    have hw1 : w ∉ S₁ := fun h' => hw (by simp [hSdef, h'])
    have hw2 : w ∉ S₂ := fun h' => hw (by simp [hSdef, h'])
    refine GlobalTheory.T.tensorLattice_mul_transpose_stable_iff F E X (a + a') Xs G.W w (mat k) (mat k⁻¹) (mat_inv_mul k) ?_ ?_ γ
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc, smul_phi_compl (hnot w hw u hu), Matrix.smul_mulVec]
      exact hS₁ w hw1 u hu hint y hy
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc_inv, smul_phi_compl (hnot w hw u hu), Matrix.smul_mulVec]
      exact hS₂ w hw2 u hu hint y hy
  refine ⟨S, S.toList.map fun v => (v, loc (idem F v) (idem_mul_self v) h), k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp [hSdef, hx]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    refine ⟨Finset.mem_toList.1 hv, ?_⟩
    intro u hu
    show u • (mat (loc (idem F v) (idem_mul_self v) h) - 1) = 0
    rw [mat_loc, phi_sub_one, smul_smul, mul_idem_of_evFin hu, zero_smul]
  · apply ua_ext
    rw [mat_mul, hl, mat_prod_loc h _ S.nodup_toList, Finset.toList_toFinset, hk, mat_loc, phi_mul_orth horth,
      add_sub_cancel, phi_one]
  · intro u hu
    rw [hk, mat_loc, phi_sub_one, smul_comm, hinf u hu, smul_zero]
  · intro w hw u hu
    have hu' := idem_mul_of_at hu
    have : u * (1 - idemS F S) = 0 := by
      calc u * (1 - idemS F S) = (idem F w * u) * (1 - idemS F S) := by rw [hu']
        _ = u * (idem F w - idem F w * idemS F S) := by ring
        _ = 0 := by rw [idem_mul_idemS_of_mem hw, sub_self, mul_zero]
    rw [hk, mat_loc, phi_sub_one, smul_smul, this, zero_smul]
  · exact fun w hw => hgood w hw a G.V
  · exact fun w hw => hgood w hw a' G.V'

end GlobalTheory.FinDecomp
end
end
