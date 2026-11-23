module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GenDataEmpty
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU

namespace UpperTheory.Gal.Gen

open GlobalTheory.CongW (IntMat wtSize HasTypeVec IsIntegralOpW)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem opOf_smul' (c : ℂ) (f : UA E a →₀ ℂ) (φ : UA E a → ℂ) : opOf (RU E a) (c • f) φ = c • opOf (RU E a) f φ := by
  have e : ∀ f : UA E a →₀ ℂ, opOf (RU E a) f φ = Finsupp.linearCombination ℂ (fun g => RU E a g φ) f := fun f =>
    (Finsupp.linearCombination_apply ℂ f).symm
  rw [e, e, map_smul]

theorem part_mono (W : Wt E a) (C : Subgroup (UA E a)) {P Q : Submodule ℂ (UA E a → ℂ) → Prop} (h : ∀ U, P U → Q U) :
    part W C P ≤ part W C Q :=
  iSup₂_le fun π hπ => le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : Q π.V) => π.finPart W ⊓ fixedBy W C) π (h _ hπ) le_rfl

end UpperTheory.Gal.Gen

end
