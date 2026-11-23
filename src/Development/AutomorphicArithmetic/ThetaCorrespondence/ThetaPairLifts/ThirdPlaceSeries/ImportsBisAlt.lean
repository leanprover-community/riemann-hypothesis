module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
namespace GlobalTheory.AdmIface
theorem main_alt_alt : ∀ D : D7, (Formalism.MainNotions.SumRepresentations.adm1 D → ∀ i, BCEx D.nd D.naut i) ∧ (Formalism.MainNotions.SumRepresentations.adm5 D → ChebSplit D.nd ∧ GlobalTheory.RowCopy.IsobaricCuspidalStrongMultiplicityOne D.nd D.naut ∧ GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut) ∧ (Formalism.MainNotions.SumRepresentations.Conclusion42 D → ∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i) ∧ (_root_.Formalism.MainNotions.SumRepresentations.adm7_alt D ↔ _root_.UpperTheory.GalN.TempCSDo D) ∧ (Formalism.MainNotions.SumRepresentations.adm3 D ↔ ∀ i, GlobalTheory.ThetaExh.SplitLift D.nd D.naut i) ∧ (Formalism.MainNotions.SumRepresentations.adm8 D ↔ Rows.IsotInternal D.what₂) := by
  intro D
  refine ⟨?_, ?_, ?_, Iff.rfl, ?_, Iff.rfl⟩
  · intro h i
    exact h i
  · rintro ⟨h1, h2, h3, -⟩
    refine ⟨?_, h1, h2⟩
    intro S
    rw [dense_iff_closure_eq]
    have := h3 (S : Set (PlE D.host)) S.finite_toSet
    simpa only [Finset.mem_coe] using this
  · intro h i σ P hP
    have hne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
      intro h0
      apply hP.1
      rw [h0, Submodule.map_bot]
    obtain ⟨-, ⟨Sig, hS, hB⟩, -⟩ := h i σ hne
    exact ⟨Sig, hS, hB P hP⟩
  · constructor
    · intro h i σ P hP w hw
      exact h i σ P hP w hw
    · intro h i σ P hP w hw
      exact h i σ P hP w hw
end GlobalTheory.AdmIface
end
