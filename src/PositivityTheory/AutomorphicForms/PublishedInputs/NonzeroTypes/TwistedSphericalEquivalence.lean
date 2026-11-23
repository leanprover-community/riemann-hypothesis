module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates
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

noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace TwistedSphericalEquivalence

theorem isTwSphProd_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k) W} (e : ρ.Equiv ρ')
    {s : ℕ} {d : Fin s → ℕ} {hd : ∑ a, d a = n} {η : Fin s → kˣ →* ℂˣ}
    (h : UpperTheory.TNZ.IsTwSphProd ρ' d hd η) : UpperTheory.TNZ.IsTwSphProd ρ d hd η := by
  obtain ⟨X, i1, i2, σ, hs, hi, hv, ⟨φ⟩⟩ := h
  exact ⟨X, i1, i2, σ, hs, hi, hv, ⟨Representation.Equiv.trans e φ⟩⟩

end TwistedSphericalEquivalence

theorem twistedSphericalRepresentative_holds : TwistedSphericalRepresentative := by
  intro k _ _ _ _ n V _ _ ρ h1 h2 s d hd η
  have e := GlobalTheory.LocGL.IrrGL.equivOf ρ h1 h2
  exact ⟨fun h => TwistedSphericalEquivalence.isTwSphProd_of_equiv e h, fun h => TwistedSphericalEquivalence.isTwSphProd_of_equiv (Representation.Equiv.symm e) h⟩

end UpperTheory.NonzeroTypeTheory
