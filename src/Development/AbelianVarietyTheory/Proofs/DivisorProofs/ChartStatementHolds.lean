module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LineNorm

namespace GlobalTheory.FlatModel

theorem exists_affine_normal_domain {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (V : X.Opens) {z : X}
    (hz : z ∈ V) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : IsDomain Γ(X, U)),
      z ∈ U ∧ U ≤ V ∧ IsIntegrallyClosed Γ(X, U) := by
  have hC : IsOpen (irreducibleComponent z) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)
  obtain ⟨U, hU, hzU, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := z)
    (U := V ⊓ ⟨irreducibleComponent z, hC⟩) ⟨hz, mem_irreducibleComponent⟩
  have hpre : IsPreirreducible (U : Set X) := (isIrreducible_irreducibleComponent (x := z)).2.open_subset U.2
    fun q hq => (hle hq).2
  have hirr : IsIrreducible (U : Set X) := ⟨⟨z, hzU⟩, hpre⟩
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hirr
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : Nonempty (Spec Γ(X, U)) := ⟨hU.isoSpec.hom ⟨z, hzU⟩⟩
  have : IsIntegral (Spec Γ(X, U)) := isIntegral_of_isOpenImmersion hU.isoSpec.inv
  have hd : IsDomain Γ(X, U) := (affine_isIntegral_iff _).1 this
  exact ⟨U, hU, hd, hzU, fun q hq => (hle hq).1,
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain _).1 (GlobalTheory.IsNormalScheme.spec_of_isAffineOpen hU)⟩

end GlobalTheory.FlatModel

end
