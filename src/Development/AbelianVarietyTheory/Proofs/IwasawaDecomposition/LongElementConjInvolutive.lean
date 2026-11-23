module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem longElt_invT_involution : ∀ (R : Type) [CommRing R] (n : ℕ) (g : GL (Fin n) R), longElt n R * GlobalTheory.CuspRep.invT n R (longElt n R * GlobalTheory.CuspRep.invT n R g * longElt n R) * longElt n R = g := by
  intro R _ n g
  have hw : longElt n R * longElt n R = 1 := Units.ext (antidiag_mul_self n R)
  have hii : ∀ h : GL (Fin n) R, GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R h) = h := fun h => by
    apply Units.ext
    show (h.valᵀ)ᵀ = h.val
    exact Matrix.transpose_transpose _
  have hwT : GlobalTheory.CuspRep.invT n R (longElt n R) = longElt n R := by
    apply Units.ext
    show (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0)ᵀ = Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    congr 1
    exact propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  rw [map_mul, map_mul, hii, hwT, ← mul_assoc, ← mul_assoc, hw, one_mul, mul_assoc, hw, mul_one]

end GlobalTheory
