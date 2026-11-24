module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.G8

theorem topo_units {R : Type} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ T2Space (GL (Fin n) R) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  have : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isEmbedding.secondCountableTopology
  have : T2Space (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isEmbedding.t2Space
  have h := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)
  exact ⟨h.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space⟩

theorem topo_thetaR_cont {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (c : R →+* R)
    (hc : Continuous c) (n : ℕ) : Continuous (thetaR c n) := by
  rw [Units.continuous_iff]
  exact ⟨(Units.continuous_coe_inv.matrix_map hc).matrix_transpose,
    (Units.continuous_val.matrix_map hc).matrix_transpose⟩

theorem topo_countable (E : Type) [Field E] [NumberField E] (n : ℕ) : Countable (GL (Fin n) E) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E))
    fun _ _ h => Units.ext h

theorem topo_thF_cont (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (thF E n) := by
  have h : ∀ g, thF E n g = PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g *
      (PhiU n (Af E))⁻¹ := fun g => thetaGL_eq n (Af E) _ g
  rw [show (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = _ from funext h]
  exact (continuous_const.mul (topo_thetaR_cont _ (continuous_conjFin _) n)).mul continuous_const

theorem topo_holds : Topo := by
  intro E _ _ _ n
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  obtain ⟨hc, hs, -⟩ := topo_units (R := ℂ) n
  exact ⟨topo_units n, topo_units n, ⟨hc, hs⟩, topo_countable E n, topo_thF_cont E n,
    topo_thetaR_cont _ Complex.continuous_conj n⟩

end PositivityTheory.Rg.BcB.G8

end
