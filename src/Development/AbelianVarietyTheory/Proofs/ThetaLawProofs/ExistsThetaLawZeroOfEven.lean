module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsSymmMulVecAddDiagModTwo
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawMul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaSqCongrModTwo
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenBase

@[expose] public section

namespace GlobalTheory.KeyPow


open Matrix ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem exists_thetaLaw_zero_of_even (hInv : ReciprocityTheory.ChartRestriction.G.Key.Chi.InversionStatement) (g : ℕ)
    (n n' : Fin g → ℤ) (h : Even (n ⬝ᵥ n')) :
    ∃ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, GlobalTheory.KeyPow.ThetaLaw g sp n n' 0 0 := by
  obtain ⟨S, hS, hd⟩ := GlobalTheory.exists_isSymm_mulVec_add_diag_mod_two g n n' h
  have h1 : ThetaLaw g (spTransl S) n n' n 0 :=
    (thetaLaw_generators hInv g n 0).1 S n' hS fun i => by simpa using hd i
  have h2 : ThetaLaw g (Matrix.J (Fin g) ℤ) n 0 0 n := (thetaLaw_generators hInv g 0 n).2
  have hD : (Matrix.diagonal n).IsSymm := Matrix.isSymm_diagonal _
  have h3 : ThetaLaw g (spTransl (Matrix.diagonal n)) 0 n 0 0 :=
    (thetaLaw_generators hInv g 0 0).1 _ n hD fun i => by simp
  have m1 : spTransl S ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hS
  have m2 : Matrix.J (Fin g) ℤ ∈ Matrix.symplecticGroup (Fin g) ℤ := SymplecticGroup.J_mem _ _
  have m3 : spTransl (Matrix.diagonal n) ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hD
  exact ⟨_, mul_mem m3 (mul_mem m2 m1), thetaLaw_mul g _ _ _ _ _ _ _ _ m3 (mul_mem m2 m1)
    (thetaLaw_mul g _ _ _ _ _ _ _ _ m2 m1 h1 h2) h3⟩

end GlobalTheory.KeyPow
