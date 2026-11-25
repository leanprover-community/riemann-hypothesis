module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SymMulPull

open GlobalTheory.MulPull

section Base

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem hasGen_theta (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) :
    HasGen L (thφ A (x3 A)) thε := by
  have := hA.comm
  obtain ⟨t, ht⟩ := hC S A hA L hL _ (x3 A 0) (x3 A 1) (x3 A 2)
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun U _ h => by
    have e := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) h
    have i : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 _ := by ext <;> simp [x3]
    rw [i] at e
    simp only [Over.id_left, Category.id_comp] at e
    rw [e, Fin.prod_univ_eight]
    simp only [Matrix.cons_val, zpow_one, zpow_neg]) t ht
  exact ⟨t', ht'⟩

end Base

end GlobalTheory.SymMulPull
