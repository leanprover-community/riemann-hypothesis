module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedRegular

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem regular_onto (h : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) :
    (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧
    (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧
    ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  refine ⟨fun K b hb hg => ?_, fun u => ?_, fun K w => ?_⟩
  · have hu : IsUnit (T.eB b) := by
      refine h.regular C K (T.eB b) (fun h0 => hb (T.eB.injective (h0.trans (map_zero _).symm))) fun g hgK => ?_
      obtain ⟨x, hx⟩ := hg g hgK
      refine ⟨x, ?_⟩
      rw [← T.actB, hx, Algebra.smul_def, map_mul,
        IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, hC.u]
      rfl
    simpa using hu.map T.eB.symm
  · obtain ⟨x, hx⟩ := GlobalTheory.Published.FontaineBcris.oneSubPhiOnto_of_filZero (h.ontoFilZero C) (T.eB u)
    refine ⟨T.eB.symm x, T.eB.injective ?_⟩
    rw [map_sub, T.frob, RingEquiv.apply_symm_apply, hx]
  · obtain ⟨x, hx, hF⟩ := h.fundOnto C (T.eD w)
    refine ⟨T.eB.symm x, T.eB.injective ?_, ?_⟩
    · rw [T.frob, RingEquiv.apply_symm_apply, hx]
    · rw [T.fil, map_sub, hC.ι, RingEquiv.apply_symm_apply]
      exact hF

end GlobalTheory.MemLoc.TiedRegular
