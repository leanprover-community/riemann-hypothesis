module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.PreOfGens
public import Development.WeilBound.LevelCriteria.IsLevOneIff
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdeal
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMap
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPMorphismOfFlatAlgebra
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ChooseFac, Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.DpOfPre, Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsLiftAndAug, Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug

-- ===== clump member: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ChooseFac =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ChooseFac", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdeal\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt\npublic import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.PreOfGens\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries

variable {B : Type} [CommRing B]

theorem e_pow (Q : PDPoly B) (l n : ℕ) :
    ∃ M : ℕ, M * l.factorial ^ n = (n * l).factorial ∧ Q.e l ^ n = (M : Q.P) * Q.e (n * l) := by
  induction n with
  | zero => exact ⟨1, by simp, by simp [Q.e_zero]⟩
  | succ n ih =>
    obtain ⟨M, h1, h2⟩ := ih
    refine ⟨M * (n * l + l).choose (n * l), ?_, ?_⟩
    · have := Nat.add_choose_mul_factorial_mul_factorial (n * l) l
      rw [← Nat.choose_symm_add] at this
      rw [Nat.succ_mul, ← this, ← h1]; ring
    · rw [pow_succ, h2, mul_assoc, Q.e_mul, Nat.succ_mul]; push_cast; ring

theorem choose_fac (a b : ℕ) : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rwa [Nat.add_sub_cancel_left] at h

theorem num1 (m n : ℕ) {K : ℕ} (hK : K ≠ 0) :
    m.uniformBell K * n.uniformBell K * (m * K + n * K).choose (m * K) =
      (m + n).choose m * (m + n).uniformBell K := by
  apply GlobalTheory.PDA.uniformBell_mul_uniformBell <;> assumption

theorem num2 (n l M : ℕ) {K : ℕ} (hK : K ≠ 0) (hM : M * l.factorial ^ n = (n * l).factorial) :
    M * n.uniformBell K * (n * l + n * K).choose (n * l) = (l + K).choose l ^ n * n.uniformBell (l + K) := by
  have h1 := Nat.uniformBell_mul_eq n hK
  have h3 := Nat.uniformBell_mul_eq n (show l + K ≠ 0 by omega)
  have h4 := choose_fac (n * l) (n * K)
  have h5 := choose_fac l K
  have hpos : 0 < l.factorial ^ n * K.factorial ^ n * n.factorial := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc _ = (n * l + n * K).choose (n * l) * (M * l.factorial ^ n) *
        (n.uniformBell K * K.factorial ^ n * n.factorial) := by ring
    _ = (n * (l + K)).factorial := by rw [h1, hM, h4, mul_add]
    _ = n.uniformBell (l + K) * ((l + K).choose l * l.factorial * K.factorial) ^ n * n.factorial := by
        rw [h5, h3]
    _ = _ := by ring

def gb (Q : PDPoly B) (K n : ℕ) : Q.P := (n.uniformBell K : Q.P) * Q.e (n * K)

theorem gb_zero (Q : PDPoly B) (K : ℕ) : gb Q K 0 = 1 := by simp [gb, Nat.uniformBell_zero_left, Q.e_zero]

theorem gb_mul (Q : PDPoly B) {K : ℕ} (hK : K ≠ 0) (m n : ℕ) :
    gb Q K m * gb Q K n = ((m + n).choose m : Q.P) * gb Q K (m + n) := by
  unfold gb
  have h := num1 m n hK
  calc ((m.uniformBell K : Q.P) * Q.e (m * K)) * ((n.uniformBell K : Q.P) * Q.e (n * K))
      = ((m.uniformBell K * n.uniformBell K * (m * K + n * K).choose (m * K) : ℕ) : Q.P) *
          Q.e (m * K + n * K) := by
        rw [mul_mul_mul_comm, Q.e_mul]
        push_cast
        ring
    _ = _ := by
        rw [h, ← add_mul]
        push_cast
        ring

theorem pre_aug (B : Type) [CommRing B] (Q : PDPoly B) : ∃ η : ℕ → Q.P → Q.P, IsPreDP Q.aug η ∧
    ∀ n k : ℕ, η n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
  apply GlobalTheory.PDA.exists_isPreDividedPowers_augmentation

end FubiniStudyChowHeightFormula₂.Adr
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ChooseFac =====

-- ===== clump member: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.DpOfPre =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.DpOfPre", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.WeilBound.LevelCriteria.IsLevOneIff\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGenerators\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtension\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

theorem dp_of_pre : ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s → (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) → ∃ δ : DividedPowers J, δ.dpow = γ :=
  @GlobalTheory.PDA.exists_dividedPowers_of_comp_on_gens

theorem dp_split : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (P : Type) [CommRing P] [Algebra B P] (ε : P →ₐ[B] B) (𝔞 : Ideal P) (η : DividedPowers 𝔞), (∀ p, p ∈ 𝔞 ↔ ε p = 0) → ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), IsDPMorphism δ θ (algebraMap B P) ∧ ∀ n, ∀ p ∈ 𝔞, θ.dpow n p = η.dpow n p :=
  @GlobalTheory.SplitDP.exists_dp_ext

end FubiniStudyChowHeightFormula₂.Adr
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.DpOfPre =====

-- ===== clump member: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsLiftAndAug =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsLiftAndAug", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMap\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {B : Type} [CommRing B]

alias e_succ_mem_aug := _root_.GlobalTheory.PDA.PDPoly.e_succ_mem_aug

def liftAlg (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) : Q.P →ₐ[B] C :=
  AlgHom.ofLinearMap (Q.e.constr B c) (by rw [← Q.e_zero, Module.Basis.constr_basis, h0]) (by
    intro x y
    have key : (LinearMap.mul B Q.P).compr₂ (Q.e.constr B c) =
        (LinearMap.mul B C).compl₁₂ (Q.e.constr B c) (Q.e.constr B c) := by
      refine Q.e.ext fun m ↦ Q.e.ext fun n ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        Module.Basis.constr_basis, Q.e_mul]
      rw [← nsmul_eq_mul, LinearMap.map_smul_of_tower, Module.Basis.constr_basis, nsmul_eq_mul, hm]
    exact congrArg (fun g ↦ g x y) key)

theorem liftAlg_e (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) (n : ℕ) :
    liftAlg Q c h0 hm (Q.e n) = c n :=
  Q.e.constr_basis B c n

theorem exists_lift_and_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 →
      (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) →
      ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧
    ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  apply GlobalTheory.PDA.PDPoly.exists_lift_and_aug

end FubiniStudyChowHeightFormula₂.Adr
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsLiftAndAug =====

-- ===== clump member: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPMorphismOfFlatAlgebra\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt\npublic import Mathlib.RingTheory.Flat.Basic\npublic import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ChooseFac\npublic import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.DpOfPre\npublic import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsLiftAndAug\nimport Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.PreOfGens\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import Mathlib.RingTheory.Flat.EquationalCriterion\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries

theorem uniformBell_comp_coeff (m : ℕ) {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) :
    n.uniformBell N ^ m * m.uniformBell (n * N) = m.uniformBell n * (m * n).uniformBell N := by
  have h1 := Nat.uniformBell_mul_eq n hN
  have h2 := Nat.uniformBell_mul_eq m (Nat.mul_ne_zero hn hN)
  have h3 := Nat.uniformBell_mul_eq m hn
  have h4 := Nat.uniformBell_mul_eq (m * n) hN
  have hpos : 0 < N.factorial ^ (m * n) * n.factorial ^ m * m.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  have e1 : n.uniformBell N ^ m * m.uniformBell (n * N)
      * (N.factorial ^ (m * n) * n.factorial ^ m * m.factorial) = (m * (n * N)).factorial := by
    rw [← h2, ← h1]
    ring
  have e2 : m.uniformBell n * (m * n).uniformBell N
      * (N.factorial ^ (m * n) * n.factorial ^ m * m.factorial) = (m * n * N).factorial := by
    rw [← h4, ← h3]
    ring
  rw [e1, e2, mul_assoc]

theorem exists_dividedPowers_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  intro B _ Q
  obtain ⟨η, hpre, hη⟩ := pre_aug B Q
  obtain ⟨δ, hδ⟩ := dp_of_pre Q.P Q.aug η (Set.range fun n : ℕ => Q.e (n + 1)) hpre rfl (by
    rintro x ⟨k, rfl⟩ m n hn
    show η m (η n (Q.e (k + 1))) = _ * η (m * n) (Q.e (k + 1))
    obtain ⟨j, hj⟩ : ∃ j, n * (k + 1) = j + 1 :=
      ⟨n * (k + 1) - 1, by
        have : 0 < n * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) k.succ_pos
        omega⟩
    have hc := congrArg (Nat.cast : ℕ → Q.P) (uniformBell_comp_coeff m hn (N := k + 1) (by omega))
    push_cast at hc
    rw [hη n k, hj, hpre.mul m _ _ (Q.e_succ_mem_aug j), hη m j, hη (m * n) k, ← hj,
      show m * (n * (k + 1)) = m * n * (k + 1) by ring, ← mul_assoc, ← mul_assoc, hc])
  refine ⟨δ, fun n => ?_⟩
  rw [hδ]
  simpa [Nat.uniformBell_one_right] using hη n 0

theorem flatExt (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] (I : Ideal R)
    (κ : DividedPowers I) : ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  apply GlobalTheory.DPFlat.exists_isDPMorphism_of_flat

theorem exists_std (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) :
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  obtain ⟨η, hη⟩ := exists_dividedPowers_aug B Q
  obtain ⟨-, ε, hε⟩ := exists_lift_and_aug B Q
  obtain ⟨θ, hθ, hθη⟩ := dp_split B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n => ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0)]
  exact hη n

end FubiniStudyChowHeightFormula₂.Adr
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug =====
