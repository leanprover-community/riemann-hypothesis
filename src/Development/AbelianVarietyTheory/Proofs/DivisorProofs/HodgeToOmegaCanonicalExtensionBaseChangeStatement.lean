module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeToOmegaCanonicalExtensionBaseChange
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

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hodgeToOmega_canonical_extension_base_change :
    ∀ (p : ℕ) [Fact p.Prime] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
      (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
      (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ),
      IsAbelianScheme A → IsAbelianScheme A' →
    ∀ (G : PDivGroup p R) (G' : PDivGroup p R') (t : G.TorsionTower A) (t' : G'.TorsionTower A')
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega) (ψ' : PrimitiveSubmodule A' →ₗ[R'] G'.omega),
      (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
      (∀ c : PrimitiveSubmodule A', PtExt.IsCan t' c.1 (G'.rigOfOmega (ψ' c))) →
    ∀ (c : PrimitiveSubmodule A)
      (hc : (GlobalTheory.Published.AbelianDeRham.bcMor h).pull c.1 ∈ PrimitiveSubmodule A'),
      ψ' ⟨_, hc⟩ = (t'.semiHom t (grpMor_of_isGrpPullback h)).omega (ψ c) :=
  @GlobalTheory.PtExt.psi_baseChange
