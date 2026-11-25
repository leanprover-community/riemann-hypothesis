module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RadialGaugeOfGaugeIdentitySlices
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates

@[expose] public section

section PartHU

open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x1

variable {k r : ℕ}

theorem hu_pull_sigmaFinite {U : Set (Mat k r)} (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) [SigmaFinite μ] :
    SigmaFinite (pull hU μ) := by
  refine (Measure.FiniteSpanningSetsIn.sigmaFinite (C := Set.univ)
    ⟨fun n => (inc : Gp U hU → Mt k r) ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩)
  · rw [pull, inc_memb.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
  · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]

theorem hu_smul {U : Set (Mat k r)} {ν : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U ν) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc1 : c ≠ ∞) : Formalism.FourierDecayAlt.B.IsHaarOn U (c • ν) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, h.conc, smul_zero]
  · intro a ha
    rw [Measure.map_smul c (lmulM_cont (k := k) (r := r) a).measurable.aemeasurable, h.left a ha]
  · intro a ha
    rw [Measure.map_smul c (rmulF_cont a).measurable.aemeasurable, h.right a ha]
  · intro K hK
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc1) (h.finite_compact K hK)
  · intro h0
    apply h.ne_zero
    ext s _
    have := congrArg (fun m : Measure (Mt k r) => m s) h0
    simp only [smul_apply, FunLike.coe_zero, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact absurd h1 hc0
    · simpa using h1

theorem hu_eq_smul {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {ν μ : Measure (Mt k r)}
    (hν : Formalism.FourierDecayAlt.B.IsHaarOn U ν) (hμ : Formalism.MainNotions.S.IsHaarOn U μ) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • ν := by
  obtain ⟨hσ, h0, hc, hl⟩ := hμ
  have hc' : μ Uᶜ = 0 := hc
  have : SigmaFinite ν := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hν
  have i1 : SigmaFinite (pull hU μ) := hu_pull_sigmaFinite hU μ
  have i2 : SigmaFinite (pull hU ν) := hu_pull_sigmaFinite hU ν
  have i3 : (pull hU μ).IsMulLeftInvariant := pull_left μ hl
  have i4 : (pull hU ν).IsMulLeftInvariant := pull_left ν hν.left
  have i5 : IsFiniteMeasureOnCompacts (pull hU ν) := pull_fin ν hν.finite_compact
  have hν0 : pull hU ν ≠ 0 := by
    intro h
    apply hν.ne_zero
    rw [← map_pull (hU := hU) ν hν.conc, h, Measure.map_zero]
  have hμ0 : pull hU μ ≠ 0 := by
    intro h
    apply h0
    rw [← map_pull (hU := hU) μ hc', h, Measure.map_zero]
  obtain ⟨K, hK, hK0⟩ := exists_pos (pull hU ν) hν0
  have hKt : pull hU ν K ≠ ∞ := hK.measure_lt_top.ne
  have key := measure_eq_div_smul (pull hU μ) (pull hU ν) hK0 hKt
  set c : ℝ≥0∞ := pull hU μ K / pull hU ν K with hcdef
  have hc0 : c ≠ 0 := by
    intro h
    apply hμ0
    rw [key, h, zero_smul]
  have hc1 : c ≠ ∞ := by
    intro h
    obtain ⟨n, hn⟩ := exists_pos_measure_of_cover (iUnion_spanningSets (pull hU μ)) hμ0
    have hfin := measure_spanningSets_lt_top (pull hU μ) n
    have e0 : ∀ s : Set (Gp U hU), pull hU μ s = ∞ * pull hU ν s := by
      intro s
      have := congrArg (fun m : Measure (Gp U hU) => m s) key
      simpa only [smul_apply, smul_eq_mul, h] using this
    have e := e0 (spanningSets (pull hU μ) n)
    by_cases hz : pull hU ν (spanningSets (pull hU μ) n) = 0
    · rw [e, hz, mul_zero] at hn
      exact lt_irrefl _ hn
    · rw [e, ENNReal.top_mul hz] at hfin
      exact lt_irrefl _ hfin
  refine ⟨c, hc0, hc1, ?_⟩
  calc μ = (pull hU μ).map inc := (map_pull μ hc').symm
    _ = (c • pull hU ν).map inc := by rw [← key]
    _ = c • ν := by rw [Measure.map_smul c inc_memb.measurable.aemeasurable, map_pull ν hν.conc]

theorem hu_general {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {ν μ : Measure (Mt k r)}
    (hν : Formalism.FourierDecayAlt.B.IsHaarOn U ν) (hμ : Formalism.MainNotions.S.IsHaarOn U μ) : Formalism.FourierDecayAlt.B.IsHaarOn U μ := by
  obtain ⟨c, hc0, hc1, rfl⟩ := hu_eq_smul hU hν hμ
  exact hu_smul hν hc0 hc1

theorem hu_haarUp :
    (∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
      Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) ∧
    ∀ (k r : ℕ) (μ : Measure (Mt k r)), Formalism.MainNotions.S.IsHaarOn (Nset k r) μ → Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μ := by
  refine ⟨fun k r z μ hz hT hμ => ?_, fun k r μ hμ => ?_⟩
  · obtain ⟨ν, hν⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
    exact hu_general (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hν hμ
  · obtain ⟨ν, hν⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
    exact hu_general (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hν hμ

theorem hu_haarG (k r : ℕ) (μ : Measure (Mt k r)) (hμ : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μ) :
    Formalism.FourierDecayAlt.B.IsHaarOn (GV k r) μ := by
  obtain ⟨ν, hν⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  exact hu_general (Formalism.FourierDecayAlt.P.unitary_group_closed k r) hν hμ

end Formalism.MainNotions.BridgeLemma₃

end

end PartHU

section PartRP

open Matrix

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.MainNotions.S

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section aux

variable {k r : ℕ}

def rp_ι (k r : ℕ) (i : Fin k) : Fin (2 * r + k + 1) := ⟨r + i.val, by have := i.2; omega⟩

def rp_blk (k r : ℕ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => m (rp_ι k r i) (rp_ι k r j)

theorem rp_mid_ι (i : Fin k) : Formalism.MainNotions.LowestKTypeMultiplicity.rp_Mid k r (rp_ι k r i) := by
  have := i.2
  constructor <;> simp only [rp_ι] <;> omega

theorem rp_ι_inj : Function.Injective (rp_ι k r) := fun a b hab =>
  Fin.ext (by have := congrArg Fin.val hab; simpa [rp_ι] using this)

theorem rp_eq_blockW (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (h : Formalism.MainNotions.LowestKTypeMultiplicity.rp_Std k r m) :
    m = blockW k r (rp_blk k r m) := by
  ext i j
  unfold blockW
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · rw [dite_eq_left hi]
    by_cases hj : r ≤ j.val ∧ j.val < r + k
    · rw [dite_eq_left hj]
      have e1 : rp_ι k r ⟨i.val - r, by omega⟩ = i := Fin.ext (by simp only [rp_ι]; omega)
      have e2 : rp_ι k r ⟨j.val - r, by omega⟩ = j := Fin.ext (by simp only [rp_ι]; omega)
      simp only [rp_blk, e1, e2]
    · rw [dite_eq_right hj, (h j hj).2 i, if_neg]
      rintro rfl
      exact hj hi
  · rw [dite_eq_right hi, (h i hi).1 j]

theorem rp_sum (f : Fin (2 * r + k + 1) → ℂ) (h : ∀ l, ¬ Formalism.MainNotions.LowestKTypeMultiplicity.rp_Mid k r l → f l = 0) :
    ∑ l, f l = ∑ i, f (rp_ι k r i) := by
  symm
  refine Fintype.sum_of_injective (rp_ι k r) rp_ι_inj _ _ ?_ (fun _ => rfl)
  intro l hl
  apply h
  intro hm
  exact hl ⟨⟨l.val - r, by have := hm.2; have := hm.1; omega⟩, Fin.ext (by simp only [rp_ι]; have := hm.1; omega)⟩

theorem rp_blk_mul (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : Formalism.MainNotions.LowestKTypeMultiplicity.rp_Std k r a) :
    rp_blk k r (a * b) = rp_blk k r a * rp_blk k r b := by
  ext i j
  simp only [rp_blk, Matrix.mul_apply]
  refine rp_sum _ fun l hl => ?_
  rw [(ha l hl).2 (rp_ι k r i), if_neg, zero_mul]
  rintro rfl
  exact hl (rp_mid_ι i)

theorem rp_blk_one : rp_blk k r 1 = 1 := by
  ext i j
  simp only [rp_blk, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun e => h (rp_ι_inj e))]

theorem rp_blk_unitary (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hU : m ∈ UH (Hpk k r))
    (hs : Formalism.MainNotions.LowestKTypeMultiplicity.rp_Std k r m) : (rp_blk k r m)ᴴ * rp_blk k r m = 1 := by
  ext i j
  have e := congrFun (congrFun (show mᴴ * Hpk k r * m = Hpk k r from hU) (rp_ι k r i)) (rp_ι k r j)
  rw [Matrix.mul_assoc, Matrix.mul_apply, Formalism.MainNotions.LowestKTypeMultiplicity.rp_H_mid _ (rp_mid_ι i)] at e
  have e2 : ∑ l, mᴴ (rp_ι k r i) l * (Hpk k r * m) l (rp_ι k r j) =
      ∑ a, mᴴ (rp_ι k r i) (rp_ι k r a) * (Hpk k r * m) (rp_ι k r a) (rp_ι k r j) :=
    rp_sum _ fun l hl => by
      rw [Matrix.conjTranspose_apply, (hs l hl).1 (rp_ι k r i), if_neg, star_zero, zero_mul]
      rintro rfl
      exact hl (rp_mid_ι i)
  have e3 : ∀ a, (Hpk k r * m) (rp_ι k r a) (rp_ι k r j) = m (rp_ι k r a) (rp_ι k r j) := by
    intro a
    rw [Matrix.mul_apply]
    simp only [Formalism.MainNotions.LowestKTypeMultiplicity.rp_H_mid _ (rp_mid_ι a), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [e2] at e
  simp only [e3] at e
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rp_blk, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply] at e
  rw [e]
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun e => h (rp_ι_inj e))]

theorem rp_blk_mem (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hU : m ∈ UH (Hpk k r))
    (hs : Formalism.MainNotions.LowestKTypeMultiplicity.rp_Std k r m) : rp_blk k r m ∈ UJset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    simp [Formalism.REAL.Jm, allPos]
  show (rp_blk k r m)ᴴ * Formalism.REAL.Jm (allPos k) * rp_blk k r m = Formalism.REAL.Jm (allPos k)
  rw [hJ, Matrix.mul_one, rp_blk_unitary m hU hs]

end aux

end Formalism.MainNotions.BridgeLemma₃

end PartRP

section PartCal

open Matrix Filter Topology

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev cal_Ix (k r : ℕ) := Fin (2 * r + k + 1) × Fin (2 * r + k + 1)

def hermitianRealPartUnit (ab : cal_Ix k r) : Mat k r := hpart1 (Hpk k r) (Matrix.single ab.1 ab.2 1)
def hermitianImagPartUnit (ab : cal_Ix k r) : Mat k r := hpart2 (Hpk k r) (Matrix.single ab.1 ab.2 1)

def cal_expE : List (cal_Ix k r) → List (ℂ × List (Mat k r))
  | [] => [(1, [])]
  | ab :: w => ((cal_expE w).map fun cv => (cv.1, hermitianRealPartUnit ab :: cv.2)) ++
      ((cal_expE w).map fun cv => (Complex.I * cv.1, hermitianImagPartUnit ab :: cv.2))

theorem cal_Hh : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
theorem cal_HH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
theorem cal_Hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv cal_HH

theorem cal_twoI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
  rw [eq_comm, eq_div_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
  linear_combination (-1 : ℂ) * Complex.I_sq

theorem cal_hpart1_lie (Z : Mat k r) : inLie k r (hpart1 (Hpk k r) Z) := by
  unfold inLie hpart1
  rw [cal_Hinv, conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    cal_Hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
  have e1 : Hpk k r * (Z * Hpk k r) * Hpk k r = Hpk k r * Z := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, cal_HH, Matrix.mul_one]
  have e2 : Hpk k r * (Hpk k r * Zᴴ * Hpk k r) = Zᴴ * Hpk k r := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc, cal_HH, Matrix.one_mul]
  rw [e1, e2]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  simp

theorem cal_hpart2_lie (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := by
  unfold inLie hpart2
  rw [cal_twoI, cal_Hinv, conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, cal_Hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]
  have e1 : Hpk k r * (Z * Hpk k r) * Hpk k r = Hpk k r * Z := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, cal_HH, Matrix.mul_one]
  have e2 : Hpk k r * (Hpk k r * Zᴴ * Hpk k r) = Zᴴ * Hpk k r := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc, cal_HH, Matrix.one_mul]
  rw [e1, e2]
  have : star (-(Complex.I / 2) : ℂ) = Complex.I / 2 := by
    simp [Complex.conj_I]
    ring
  rw [this, neg_smul, add_comm (Hpk k r * Z)]
  simp

theorem hermitian_real_part_index_lie (ab : cal_Ix k r) : inLie k r (hermitianRealPartUnit ab) := cal_hpart1_lie _
theorem hermitian_imag_part_index_lie (ab : cal_Ix k r) : inLie k r (hermitianImagPartUnit ab) := cal_hpart2_lie _

theorem cal_expE_lie (w : List (cal_Ix k r)) : ∀ cv ∈ cal_expE w, ∀ X ∈ cv.2, inLie k r X := by
  induction w with
  | nil => intro cv h; simp [cal_expE] at h; simp [h]
  | cons ab w ih =>
    intro cv h X hX
    simp only [cal_expE, List.mem_append, List.mem_map] at h
    rcases h with ⟨cv', h', rfl⟩ | ⟨cv', h', rfl⟩
    · rcases List.mem_cons.1 hX with rfl | hX
      · exact hermitian_real_part_index_lie ab
      · exact ih cv' h' X hX
    · rcases List.mem_cons.1 hX with rfl | hX
      · exact hermitian_imag_part_index_lie ab
      · exact ih cv' h' X hX

end Formalism.MainNotions.BridgeLemma₃

end

end PartCal

section PartCal2

open Matrix Filter Topology

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

section Frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing

end Frob

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Formalism.MainNotions.BridgeLemma₃

end

end PartCal2

section PartCCI

open Matrix Filter Topology

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₃

end

end PartCCI

section PartAdj0

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cls

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end cls

section poly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end poly

open Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj0

section PartAdj1

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

section partA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end partA

section partB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end partB

section partC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end partC

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj1

section PartAdj2a

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj2a

section PartAdj2b

open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj2b

section PartAdj2

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section core

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]


end core

section packet

open Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end packet

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj2

section PartAdj3

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end gen

section adj

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end adj

section helpers

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end helpers

section core

open Formalism.FourierDecayAlt.P

variable {k r : ℕ}

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end core

section core2

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end core2

section core3

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end core3

section packet

open Formalism.FourierDecayAlt.P Formalism.MainNotions.S.TopsChoicePartA

end packet

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj3

section PartAdj6a

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj6a

section PartCont

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.MainNotions Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.BridgeLemma₅

theorem lbHaarUp_proved : lbHaarUp := hu_haarUp

theorem lbRepOfHC_proved : lbRepOfHC := Formalism.MainNotions.LowestKTypeMultiplicity.rp_repOfHC

end Formalism.MainNotions.BridgeLemma₃

end PartCont

section PartAdj6bP

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj6bP

section PartRad0

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end gen

section adj

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end adj

section helpers

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end helpers

end Formalism.MainNotions.BridgeLemma₃

end

end PartRad0

section PartRad1

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end Formalism.MainNotions.BridgeLemma₃

end

end PartRad1

section PartRad2

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end Formalism.MainNotions.BridgeLemma₃

end

end PartRad2

section PartRad3

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₃

end

end PartRad3

section PartOrb0

open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrb0

section PartOrbGD

open Matrix MeasureTheory

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section step

variable (k r' : ℕ) (c : ℂ) (g₁ : Mat k r')

end step

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbGD

section PartOrbCB

open Matrix MeasureTheory

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbCB

section PartOrbNB

open Matrix

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbNB

section PartOrbNI

open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbNI

section PartOrbOD1

open Matrix MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbOD1

section PartOrbOD2

open Matrix MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbOD2

section PartOrbOD

open Matrix MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbOD

section PartPX

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.MainNotions Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₃

end PartPX
