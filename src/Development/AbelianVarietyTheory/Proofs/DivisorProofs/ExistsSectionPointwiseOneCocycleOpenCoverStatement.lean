module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPointwiseOneCocycleOpenCover
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_section_pointwiseOneCocycle_openCover :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u →
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
        ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E,
          ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
            (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'),
            Sm (D := E) W (spOver ψ ≫ x) →
              σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) :=
  @GlobalTheory.PtExt.CocSec.exists_section
