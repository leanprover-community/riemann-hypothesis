module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
namespace GlobalTheory.SuppDen

variable {F : Type} [Field F] [NumberField F]

theorem norm_le_one_iff_mem (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    ‖y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

def denSet (κ : Type) (m : ℕ) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), ‖(m : v.adicCompletion F) * y i v‖ ≤ 1}

theorem isOpen_denSet (κ : Type) [Finite κ] (m : ℕ) : IsOpen (denSet (F := F) κ m) := by
  have h : denSet (F := F) κ m = ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      (m : FiniteAdeleRing (𝓞 F) F) * y i) ⁻¹'
      {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [denSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, _root_.GlobalTheory.AdeleDenominators.natCast_mul_apply,
      norm_le_one_iff_mem]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_integral.preimage ((continuous_const_mul _).comp (continuous_apply i))

theorem norm_mul_le_one_of_dvd {v : HeightOneSpectrum (𝓞 F)} {m m' : ℕ} (hd : m ∣ m')
    {z : v.adicCompletion F} (hz : ‖(m : v.adicCompletion F) * z‖ ≤ 1) :
    ‖(m' : v.adicCompletion F) * z‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul, mul_comm (m : v.adicCompletion F), mul_assoc, norm_mul]
  exact mul_le_one₀ (_root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one v k) (norm_nonneg _) hz

theorem denSet_mono (κ : Type) {m m' : ℕ} (hd : m ∣ m') :
    denSet (F := F) κ m ⊆ denSet κ m' :=
  fun _ hy i v => norm_mul_le_one_of_dvd hd (hy i v)

theorem exists_denom (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : ℕ, 0 < d ∧ ∀ v : HeightOneSpectrum (𝓞 F), ‖(d : v.adicCompletion F) * a v‖ ≤ 1 := by
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖a v‖₊).Finite := by
    apply (Filter.eventually_cofinite.1 a.2).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro hmem
    apply hv
    have : ‖a v‖ ≤ 1 := (norm_le_one_iff_mem v _).2 hmem
    exact max_eq_left (by exact_mod_cast this)
  obtain ⟨d, hd, -, h⟩ := _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator (F := F)
    (fun v => max 1 ‖a v‖₊) (fun v => le_max_left _ _) hf
  exact ⟨d, hd, fun v => h v _ (le_max_right _ _)⟩

theorem exists_mem_denSet (κ : Type) [Fintype κ] (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, 0 < m ∧ y ∈ denSet κ m := by
  classical
  choose d hd h using fun i => exists_denom (y i)
  exact ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i v =>
    norm_mul_le_one_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) (h i v)⟩

theorem support_bounded_denominators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 →
      ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1 := by
  classical
  have hK : IsCompact (tsupport g) := hg.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n : ℕ => denSet (F := F) κ (n + 1))
    (fun n => isOpen_denSet κ _) (fun y _ => by
      obtain ⟨m, hm, hy⟩ := exists_mem_denSet κ y
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
      exact Set.mem_iUnion.2 ⟨n, by simpa using hy⟩)
  refine ⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun n _ => n.succ_pos, fun x hx i v => ?_⟩
  have hy : (fun i => (x i).2) ∈ tsupport g := subset_tsupport _ hx
  obtain ⟨n, hn, hyn⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact denSet_mono κ (Finset.dvd_prod_of_mem (fun n : ℕ => n + 1) hn) hyn i v

end GlobalTheory.SuppDen
