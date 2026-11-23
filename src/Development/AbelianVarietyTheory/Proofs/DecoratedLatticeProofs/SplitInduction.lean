module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.VacConst

theorem suppAt_one {D : D7} (e : Formalism.L2.Theta.AE D) (V : HSp D) : Formalism.L2.Theta.SuppAt e V 1 := by
  intro i j
  have h : mt V 1 - 1 = 0 := by rw [GlobalTheory.AdelicLatMove.mt_one, sub_self]
  rw [h, Matrix.zero_apply, mul_zero]

theorem split_induction {D : D7} (V : HSp D) (P : GA D V → Prop)
    (hP : ∀ g ∈ GfC V, P g → ∀ e, IsSplitIdem D e → ∀ s, Formalism.L2.Theta.SuppAt e V s → P (s * g))
    {s : GA D V} (hs : s ∈ splitPart V) : s ∈ GfC V ∧ ∀ g ∈ GfC V, P g → P (s * g) := by
  induction hs using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨e, he, hx⟩ := hx
    exact ⟨GlobalTheory.SplitHecke.Stab.mem_GfC he hx, fun g hg h => hP g hg h e he x hx⟩
  | inv_mem x hx =>
    obtain ⟨e, he, hx⟩ := hx
    have hx' := GlobalTheory.SplitHecke.Stab.suppAt_inv hx
    exact ⟨GlobalTheory.SplitHecke.Stab.mem_GfC he hx', fun g hg h => hP g hg h e he _ hx'⟩
  | one => exact ⟨one_mem _, fun g _ h => by rwa [one_mul]⟩
  | mul x y _ _ ihx ihy =>
    refine ⟨mul_mem ihx.1 ihy.1, fun g hg h => ?_⟩
    rw [mul_assoc]
    exact ihx.2 _ (mul_mem ihy.1 hg) (ihy.2 g hg h)

end GlobalTheory.AdForm.VacConst
