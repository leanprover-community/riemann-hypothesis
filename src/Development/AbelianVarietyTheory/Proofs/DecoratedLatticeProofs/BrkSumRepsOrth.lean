module

public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem brk_sum_reps_orth : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ → ∀ SB : Finset V, Formalism.L2.Th1.H.IsReps Λ B SB → ∀ w ∈ Λ ⊓ A, ∑ y ∈ SB, brk H y w = if w ∈ B then (SB.card : ℂ) else 0 := by
  intro V _ _ H α A B Λ hyp SB hSB w hw
  obtain ⟨hH, -, hB, -, sdB, hΛ, -, -, -, -⟩ := hyp
  have hBint := (Formalism.L2.Th1.H.semicharacterBasic V H hH B α hB).2.2
  have hΛint := (Formalism.L2.Th1.H.semicharacterBasic V H hH Λ α hΛ).2.2
  have hwΛ : w ∈ Λ := (AddSubgroup.mem_inf.1 hw).1
  by_cases hwB : w ∈ B
  · rw [if_pos hwB, Finset.sum_congr rfl fun y hy => brk_one_of_int H (hBint hwB y (hSB.1 y hy))]
    simp
  · rw [if_neg hwB]
    have hnd : w ∉ Formalism.L2.Th1.H.dualLat H B := by rw [sdB]; exact hwB
    have hex : ∃ y₀ ∈ B, ¬ ∃ m : ℤ, Formalism.L2.Th1.H.altE H w y₀ = (m : ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact hnd (fun y hy => hcon y hy)
    obtain ⟨y₀, hy₀B, hy₀⟩ := hex
    exact char_sum_zero hSB (fun y => brk H y w) (fun u v => brk_add_left H u v w)
      (fun m _ hmΛ => brk_one_of_int H (hΛint hwΛ m hmΛ)) (x₀ := y₀) hy₀B
      (fun h => hy₀ (int_of_brk_one H h))

end GlobalTheory
