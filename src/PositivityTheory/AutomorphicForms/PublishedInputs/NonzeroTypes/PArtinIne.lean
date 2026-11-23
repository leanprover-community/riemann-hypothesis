module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace P_artinIne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem val_ine (ha : IsLocalArtin h a) (t : Ine (F := E) A) :
    valuation (w.adicCompletion E) ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
  have h0 := ha.ord_eq (ineIncl h t)
  rw [deg_ineIncl, neg_zero] at h0
  exact ord_eq_zero_iff.mp h0

theorem exists_ine (ha : IsLocalArtin h a) (u : (w.adicCompletion E)ˣ)
    (hu : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1) :
    ∃ t : Ine (F := E) A, a (ineIncl h t) = u := by
  obtain ⟨σ, hσ⟩ := ha.surj u
  have h0 := ha.ord_eq σ
  rw [hσ, ord_eq_zero hu] at h0
  have hd : deg σ = 0 := by omega
  refine ⟨⟨(σ : G E Ω), deg_eq_zero_iff.mp hd⟩, ?_⟩
  have e : ineIncl h ⟨(σ : G E Ω), deg_eq_zero_iff.mp hd⟩ = σ := Subtype.ext rfl
  rw [e, hσ]

end P_artinIne

theorem step_artinIne : ArtinInertiaProp := by
  intro E Ω _ _ _ _ _ A w h a ha
  exact ⟨P_artinIne.val_ine ha, P_artinIne.exists_ine ha⟩

end UpperTheory.TNZ
