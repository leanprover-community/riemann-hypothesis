module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHilbertLatticeTwistIffLiftStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam.TwistMul

variable {F : Type} [Field F] [NumberField F]

theorem std_vecMul_int (A : Matrix (Fin 2) (Fin 2) ℤ) {y : Fin 2 → F} (hy : y ∈ stdLat F) :
    Matrix.vecMul y (A.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h : ∀ i, y i * ((A i j : ℤ) : F) ∈ (1 : Submodule (𝓞 F) F) := fun i ↦ by
    have := Submodule.smul_of_tower_mem (1 : Submodule (𝓞 F) F) (A i j) (hy i (Set.mem_univ i))
    rwa [zsmul_eq_mul, mul_comm] at this
  have e : Matrix.vecMul y (A.map (Int.cast : ℤ → F)) j = y 0 * ((A 0 j : ℤ) : F) + y 1 * ((A 1 j : ℤ) : F) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  change Matrix.vecMul y (A.map (Int.cast : ℤ → F)) j ∈ (1 : Submodule (𝓞 F) F)
  rw [e]
  exact Submodule.add_mem _ (h 0) (h 1)

theorem std_natCast_smul (N : ℕ) {y : Fin 2 → F} (hy : y ∈ stdLat F) : (N : F) • y ∈ stdLat F := by
  rw [Nat.cast_smul_eq_nsmul]
  exact Submodule.smul_of_tower_mem _ N hy

theorem twist_twist : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F)
    (α β : Matrix (Fin 2) (Fin 2) (ZMod N)), L ≤ stdLat F → twist N (twist N L α) β = twist N L (α * β) := by
  intro F _ _ _ N L α β hL
  have lift : ∀ γ : Matrix (Fin 2) (Fin 2) (ZMod N), ∃ C : Matrix (Fin 2) (Fin 2) ℤ, C.map (Int.cast : ℤ → ZMod N) = γ :=
    fun γ ↦ ⟨γ.map (ZMod.cast : ZMod N → ℤ), by ext i j; simp⟩
  obtain ⟨A, rfl⟩ := lift α
  obtain ⟨B, rfl⟩ := lift β
  have hm : A.map (Int.cast : ℤ → ZMod N) * B.map (Int.cast : ℤ → ZMod N) = (A * B).map (Int.cast : ℤ → ZMod N) :=
    (Matrix.map_mul (f := Int.castRingHom (ZMod N))).symm
  have hF : (A * B).map (Int.cast : ℤ → F) = A.map (Int.cast : ℤ → F) * B.map (Int.cast : ℤ → F) :=
    Matrix.map_mul (f := Int.castRingHom F)
  have hT : twist N L (A.map (Int.cast : ℤ → ZMod N)) ≤ stdLat F := by
    intro v hv
    obtain ⟨y, hy, w, hw, rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A v hL).1 hv
    exact Submodule.add_mem _ (std_vecMul_int A (hL hy)) (std_natCast_smul N hw)
  rw [hm]
  ext v
  rw [GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ B v hT, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L (A * B) v hL, hF]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    obtain ⟨y, hy, w', hw', rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A u hL).1 hu
    refine ⟨y, hy, Matrix.vecMul w' (B.map (Int.cast : ℤ → F)) + w,
      Submodule.add_mem _ (std_vecMul_int B hw') hw, ?_⟩
    rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.smul_vecMul, smul_add, add_assoc]
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨Matrix.vecMul y (A.map (Int.cast : ℤ → F)),
      (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).2 ⟨y, hy, 0, Submodule.zero_mem _, by simp⟩, w, hw, ?_⟩
    rw [Matrix.vecMul_vecMul]

end GlobalTheory.HilbFam.TwistMul
