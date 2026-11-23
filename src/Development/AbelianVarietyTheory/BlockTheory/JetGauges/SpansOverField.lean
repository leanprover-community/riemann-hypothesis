module

public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement

open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm


variable (E : Type) [Field E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]


section PhiC

variable (E : Type) [Field E] [NumberField E] [IsCMField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

abbrev bar (a : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E a

def outer {n : ℕ} (x x' : Fin n → X) (η η' : Module.Dual (𝓞 E) X) : 𝓞 E :=
  ∑ i, η (x i) * bar E (η' (x' i))

def IsPosHerm (l : Module.Dual (𝓞 E) X → Module.Dual (𝓞 E) X → 𝓞 E) : Prop :=
  (∀ η η', l η' η = bar E (l η η')) ∧
    ∀ η, η ≠ 0 → ∀ τ : E →+* ℂ, 0 < (τ (l η η : E)).re

def pairing (B : X → X → ℝ) {n : ℕ} (x x' : Fin n → X) : ℝ := (∑ i, B (x i) (x' i)) / 2

def phiC (B : X → X → ℝ) : EReal :=
  sInf {t : EReal | ∃ (n : ℕ) (x x' : Fin n → X), IsPosHerm E (outer E x x') ∧ t = (pairing B x x' : ℝ)}

end PhiC

end GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement
