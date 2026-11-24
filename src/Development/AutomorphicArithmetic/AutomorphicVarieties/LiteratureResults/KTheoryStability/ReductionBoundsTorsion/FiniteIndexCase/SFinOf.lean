module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.FgShift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.HglFGOf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField UpperTheory.V.KT UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

theorem sFin_of : SBridge → SFin := by
  intro h L _ _ hL N k
  classical
  obtain ⟨θ, hsurj, hker, -⟩ := h k
  haveI : Module.Finite ℤ (grpH (Gm L N) (k + 1)) :=
    UpperTheory.FiniteGenerationAndTorsion.hglFG_of UpperTheory.FiniteGenerationAndTorsion.fgShift L hL N (k + 1)
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℝ (ℝ ⊗[ℤ] ↑(grpH (Gm L N) (k + 1)))).FG)
  choose pre hpre using hsurj (Gm L N)
  refine ⟨t.image (fun m => ((pre m : ↥(bd (Gm L N) k).ker) : Chn (Gm L N) (k + 1))), ?_, ?_⟩
  · intro z hz
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hz
    exact LinearMap.mem_ker.mp (pre m).2
  · intro z hz
    have hz' : z ∈ LinearMap.ker (bd (Gm L N) k) := LinearMap.mem_ker.mpr hz
    have hw : θ (Gm L N) ⟨z, hz'⟩ ∈ Submodule.span ℝ (θ (Gm L N) '' (pre '' (t : Set _))) := by
      rw [Set.image_image]
      simp only [hpre, Set.image_id']
      rw [ht]
      trivial
    rw [← Submodule.map_span] at hw
    obtain ⟨u, hu, hθ⟩ := hw
    refine ⟨(u : Chn (Gm L N) (k + 1)), ?_, ?_⟩
    · have hmem : (u : Chn (Gm L N) (k + 1)) ∈
          Submodule.map (LinearMap.ker (bd (Gm L N) k)).subtype (Submodule.span ℝ (pre '' (t : Set _))) :=
        ⟨u, hu, rfl⟩
      rw [Submodule.map_span, Set.image_image] at hmem
      simpa [Finset.coe_image] using hmem
    · have h0 : θ (Gm L N) (⟨z, hz'⟩ - u) = 0 := by
        rw [map_sub, hθ, sub_self]
      exact (hker (Gm L N) _).mp h0

end PositivityTheory.KB

end
