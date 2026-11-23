module

public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2.NG

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

def SatAt (π : AutRep L n) {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (α : Fin (n / 2) → ℂ) : Prop :=
  ∃ f ∈ π.S, f ≠ 0 ∧ ∃ U : Subgroup (GAf L n), (∀ κ ∈ U, rt L n κ f = f) ∧
    (∀ κ, TrivOutside (L := L) {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧
    ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n),
      heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV L⁺ v) h α • f

end Formalism.L2.NG
