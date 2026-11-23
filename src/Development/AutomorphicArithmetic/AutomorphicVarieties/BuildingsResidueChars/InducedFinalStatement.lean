module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.ConjugateSelfDual IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd.S2

section

variable {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R')

private theorem fin_adj (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext a b
  simp only [adj_apply, Matrix.map_apply, map_zsmul]

private theorem fin_conj (X Y : M4 R) : adj (X.map j) * Y.map j * X.map j = (adj X * Y * X).map j := by
  rw [fin_adj, Matrix.map_mul, Matrix.map_mul]

private theorem fin_gsp (hj : Function.Injective j) (ν : R) (X : M4 R) (h : IsGSp (j ν) (X.map j)) : IsGSp ν X := by
  unfold IsGSp at h ⊢
  rw [fin_adj, ← Matrix.map_mul] at h
  ext a b
  apply hj
  have h1 := congrFun (congrFun h a) b
  rw [Matrix.map_apply] at h1
  rw [h1]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul]
  split_ifs <;> simp

private theorem fin_psi {ι Γ : Type} [Group Γ] (P : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) :
    (P.map j).ψ v i s = j (P.ψ v i s) :=
  congrFun (congrFun (fin_conj j (P.n v) (P.r s)) i) i

end

private theorem fin_q (i j : Fin 4) (h : i ≠ j) (h' : wt i j ∉ qQ) : i < j ∨ (i = 2 ∧ j = 1) := by
  revert i j; decide

private theorem fin_v (w : ℤ × ℤ) (h : w ∉ nP) : w ∉ vV := by
  simp only [nP, vV, Finset.mem_insert, Finset.mem_singleton] at h ⊢
  tauto
