module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Bridge
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.ValuationLeOneOfNabsLt
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.CellA



theorem openCell (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.OpenCell k := by
  intro ψ hψ _ r m V W _ _ _ _ A x ω hA hx hgA hgx hxω z hz
  obtain ⟨φ⟩ := bridge_equiv (k := k) A x
  have hs : ∀ a, IsSmooth (piPair A x a) := fun a => by
    fin_cases a
    · exact hA
    · exact hx
  obtain ⟨F, hF, hi⟩ := openCellPar ψ hψ (piTensor (piPair A x)) (isSmooth_piTensor hs) ω
    (piPair_levZ A x ω hxω) (exists_not_mem_twKer ψ A x hgA hgx) z hz
  have e : φ (φ.symm F) = F := by
    first
      | exact φ.apply_symm_apply F
      | exact φ.toLinearEquiv.apply_symm_apply F
      | simp
  refine ⟨φ.symm F, φ.symm F, fun hmem => hF ?_, 0, fun i _ => ?_⟩
  · have := (equiv_mem_twKer φ _ _ (φ.symm F)).2 hmem
    rw [e] at this
    exact this
  · rw [← equiv_mem_twKer φ]
    change φ.toIntertwiningMap _ ∈ _
    rw [map_sub, map_smul]
    change φ _ - _ • φ _ ∈ _
    rw [equiv_apply, e]
    exact hi i

end PositivityTheory.RgUd.CellA
