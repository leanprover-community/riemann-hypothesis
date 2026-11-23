module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HOption
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HomogeneousTraceDiagonal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.TrProd
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem tr1_two_eq_hq_trace_det (g : GL (Fin 2) ℂ) (n : ℕ) :
    tr1 2 n g = hq (↑g : Matrix (Fin 2) (Fin 2) ℂ).trace (↑g : Matrix (Fin 2) (Fin 2) ℂ).det n := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := ↑g with hA
  have hs : A.charpoly.Splits := IsAlgClosed.splits _
  have hcard : Multiset.card A.charpoly.roots = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have hp : A.charpoly = ∏ i, (X - C (![a, b] i)) := by
    rw [hs.eq_prod_roots_of_monic (Matrix.charpoly_monic A), hab]
    simp [Fin.prod_univ_two]
  have htr : A.trace = a + b := by
    rw [Matrix.trace_eq_sum_roots_charpoly, hab]; simp
  have hdet : A.det = a * b := by
    rw [Matrix.det_eq_prod_roots_charpoly, hab]; simp
  rw [trOne 2 n g ![a, b] hp, hqTwo, htr, hdet]

theorem UpperTheory.V.Z.Sym.Wt.trDC :
    UpperTheory.V.Z.Sym.Wt.TrDC := by
  intro I _ n e g
  rw [repD_apply, map_smul, smul_eq_mul]
  have h := trProd I 2 (fun _ => n) g
  simp only [VD] at *
  rw [h]
  simp only [detE, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    Matrix.GeneralLinearGroup.val_det_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => by rw [tr1_two_eq_hq_trace_det]
