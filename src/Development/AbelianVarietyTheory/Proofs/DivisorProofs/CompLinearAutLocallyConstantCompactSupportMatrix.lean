module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem comp_linearAut_smooth_compact : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (L (x + y)) = φ (L x)) ∧ HasCompactSupport (fun x => φ (L x)) ∧ LocallyCompactSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := by
  intro E _ _ w a b L φ hdet hlc hcs
  haveI hMT : IsModuleTopology (w.adicCompletion E) (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    inferInstanceAs (IsModuleTopology (w.adicCompletion E) (Fin a → Fin b → w.adicCompletion E))
  haveI hLC : LocallyCompactSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → w.adicCompletion E))
  let e := LinearMap.equivOfDetNeZero L hdet
  have he : ∀ x, e x = L x := fun x => rfl
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : Matrix (Fin a) (Fin b) (w.adicCompletion E) ≃ₜ Matrix (Fin a) (Fin b) (w.adicCompletion E) :=
    { toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  obtain ⟨U, hUo, hU⟩ := hlc
  refine ⟨⟨U.comap L.toAddMonoidHom, ?_, ?_⟩, ?_, hLC⟩
  · exact hUo.preimage (IsModuleTopology.continuous_of_linearMap L)
  · intro x y hy
    rw [map_add (f := _)]
    exact hU (L x) (L y) hy
  · exact hcs.comp_homeomorph h

end GlobalTheory.LeviDesc
