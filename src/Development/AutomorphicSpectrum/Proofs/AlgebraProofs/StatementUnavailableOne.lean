module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsMonogenicSeparating
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem block_monogenic_of_residual_character : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (emb : (E →+* C) → (𝓞 E →+* V)), (∀ s (a : 𝓞 E), algebraMap V C (emb s a) = s (a : E)) → Nat.card (E →+* C) = Module.finrank ℚ E → ∀ σ : E →+* C, ∃ π : 𝓞 E, (∀ s s' : E →+* C, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → (∀ a, ¬ IsUnit (emb s' a - emb σ a)) → emb s π = emb s' π → s = s') ∧ ∀ f : (E →+* C) → V, (∀ s, (∃ a, IsUnit (emb s a - emb σ a)) → f s = 0) → ((∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
  exact @PositivityTheory.Xgn.exists_monogenic_separating

end GlobalTheory.CompanionTheory.Ar.Flat
