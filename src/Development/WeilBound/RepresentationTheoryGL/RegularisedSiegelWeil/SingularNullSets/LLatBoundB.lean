module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
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
import Mathlib.Tactic.Linter.Style
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

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem tsum_GQ (V : HSp D) (n : ℕ) (γ : GA D V) (hγ : γ ∈ GQ V) (F : Mx D V.rank n → ℝ≥0∞) :
    ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F (mm (mt V γ) (rat x.1)) =
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F (rat x.1) := by
  obtain ⟨g, hg⟩ := mem_ratMx.1 ((mem_GQ_iff V γ).1 hγ)
  obtain ⟨g', hg'⟩ := mem_ratMx.1 ((mem_GQ_iff V γ⁻¹).1 (inv_mem hγ))
  have h1 : g' * g = 1 := rat_injective (by rw [rat_mul, hg, hg', rat_one]; exact mt_inv_mul V γ)
  have h2 : g * g' = 1 := rat_injective (by rw [rat_mul, hg, hg', rat_one]; exact mt_mul_inv V γ)
  have hu : IsUnit g.det := isUnit_iff_exists_inv.2 ⟨g'.det, by rw [← Matrix.det_mul, h2, Matrix.det_one]⟩
  have hu' : IsUnit g'.det := isUnit_iff_exists_inv.2 ⟨g.det, by rw [← Matrix.det_mul, h1, Matrix.det_one]⟩
  let e : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank} ≃
      {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank} :=
    { toFun := fun x => ⟨g * x.1, by rw [Matrix.rank_mul_eq_right_of_isUnit_det g x.1 hu]; exact x.2⟩
      invFun := fun x => ⟨g' * x.1, by rw [Matrix.rank_mul_eq_right_of_isUnit_det g' x.1 hu']; exact x.2⟩
      left_inv := fun x => Subtype.ext (by simp only [← Matrix.mul_assoc, h1, Matrix.one_mul])
      right_inv := fun x => Subtype.ext (by simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]) }
  rw [← e.tsum_eq (fun x => F (rat x.1))]
  refine tsum_congr fun x => ?_
  show F _ = F (rat (g * x.1))
  rw [rat_mul, hg]

end PositivityTheory.Rg.Rsw.L.LLatBound

end
