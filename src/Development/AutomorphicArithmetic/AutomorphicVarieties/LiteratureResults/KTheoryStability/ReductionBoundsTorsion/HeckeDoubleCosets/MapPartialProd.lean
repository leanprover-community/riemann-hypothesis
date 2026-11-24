module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

variable {G H K Y : Type} [Group G] [Group H] [Group K] [MulAction H Y]

theorem map_partialProd {M M' : Type} [Monoid M] [Monoid M'] (f : M →* M') {m : ℕ} (g : Fin m → M)
    (j : Fin (m + 1)) : f (Fin.partialProd g j) = Fin.partialProd (fun i => f (g i)) j := by
  induction j using Fin.inductionOn with
  | zero => simp
  | succ i ih => rw [Fin.partialProd_succ, Fin.partialProd_succ, map_mul, ih]

theorem ev_eq (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ F y z = Finsupp.linearCombination ℝ (fun g : Fin m → G => F fun j => ρ (Fin.partialProd g j) • y) z := by
  simp [ev, Finsupp.linearCombination_apply, smul_eq_mul]

theorem ev_add (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z z' : Chn G m) :
    ev ρ F y (z + z') = ev ρ F y z + ev ρ F y z' := by
  simp only [ev_eq, map_add (f := _)]

theorem ev_sub (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z z' : Chn G m) :
    ev ρ F y (z - z') = ev ρ F y z - ev ρ F y z' := by
  simp only [ev_eq, map_sub]

theorem ev_smul (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (c : ℝ) (z : Chn G m) :
    ev ρ F y (c • z) = c * ev ρ F y z := by
  rw [ev_eq, ev_eq, map_smul, smul_eq_mul]

theorem ev_zero (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) : ev ρ F y 0 = 0 := by
  simp [ev]

theorem ev_single (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (g : Fin m → G) (a : ℝ) :
    ev ρ F y (Finsupp.single g a) = a * F fun j => ρ (Fin.partialProd g j) • y := by
  simp [ev]

theorem ev_cmap (ρ : G →* H) (f : K →* G) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn K m) :
    ev ρ F y (cmap f m z) = ev (ρ.comp f) F y z := by
  simp only [cmap, Finsupp.lmapDomain_apply, ev]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  exact Finsupp.sum_congr fun g _ => by simp [MonoidHom.comp_apply, map_partialProd]

end PositivityTheory.KB.AffineStabilizerVanishing

end
