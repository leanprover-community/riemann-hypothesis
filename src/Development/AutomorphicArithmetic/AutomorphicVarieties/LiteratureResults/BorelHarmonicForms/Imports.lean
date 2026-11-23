module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
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

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.count :
    UpperTheory.V.Lit.Bor.Count := by
  classical
  intro X S deg κ hκ
  have hq : ∀ q, Cardinal.mk {x : S // deg x = q} ≤ κ q := by
    intro q
    let e := Fintype.equivFin {x : S // deg x = q}
    rw [Cardinal.mk_fintype]
    refine hκ q _ (fun i => ((e.symm i).1 : X)) ?_ (fun i => ⟨(e.symm i).1.2, (e.symm i).2⟩)
    intro i j hij
    exact e.symm.injective (Subtype.ext (Subtype.ext hij))
  calc (S.card : Cardinal) = Cardinal.mk S := (Cardinal.mk_coe_finset).symm
    _ = Cardinal.mk (Σ q, {x : S // deg x = q}) :=
        (Cardinal.mk_congr (Equiv.sigmaFiberEquiv (fun x : S => deg x))).symm
    _ = Cardinal.sum (fun q => Cardinal.mk {x : S // deg x = q}) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum κ := Cardinal.sum_le_sum _ _ hq
