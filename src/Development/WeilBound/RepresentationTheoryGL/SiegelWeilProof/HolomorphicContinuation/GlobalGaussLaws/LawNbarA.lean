module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GramXDiag
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.NbarH

variable {m n : ℕ}

theorem ftLoc_const_mul (ε : Fin m → Bool) (s : ℝ) (k : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε s (fun v => k * g v) u = k * ftLoc ε s g u := by
  unfold ftLoc
  simp_rw [mul_assoc]
  exact MeasureTheory.integral_const_mul k _

theorem ftLoc_const_mul' (ε : Fin m → Bool) (s : ℝ) (k : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) :
    ftLoc ε s (fun v => k * g v) = fun u => k * ftLoc ε s g u := funext fun u => ftLoc_const_mul ε s k g u

theorem sigR_sq (ε : Fin m → Bool) (a : Fin m) : (VacC.sigR ε a : ℂ) ^ 2 = 1 := by
  unfold VacC.sigR; split_ifs <;> norm_num

theorem ftLoc_vac (ε : Fin m → Bool) (t c s : ℝ) (hc : 0 < c) (hs : s ^ 2 = c ^ 2) :
    ftLoc ε s (vac ε t c) = fun u => ((Real.pi : ℂ) / c) ^ (m * n) * vac (n := n) ε t c u := by
  funext u
  have hs' : (s : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast hs
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [VacC.ftLoc_eq, VacC.vac_eq, VacS.ftG_DG _ _ _ _ (fun a j => by simpa using hc)]
  have hγ : (fun (a : Fin m) (j : Fin n) => (s : ℂ) ^ 2 * ((VacC.sigR ε a : ℝ) : ℂ) ^ 2 / (c : ℂ)) = fun _ _ => (c : ℂ) := by
    funext a j
    rw [sigR_sq, hs']
    field_simp
  rw [hγ]
  simp only [VacS.DG, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul]
  rw [← pow_mul, mul_comm n m]

end PositivityTheory.Rg.Sw.Glob.NbarH
