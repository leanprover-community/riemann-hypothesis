module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLiftsOverSquareZeroThickeningStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem pre_nonempty : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀), (∀ T, Algebra.Smooth R₀ (F.obj T)) → Nonempty (Pre I π F) := by
  intro R R₀ _ _ I hI π hπ hk C _ F hF
  have h := fun T => GlobalTheory.T.smoothAlgebra_lifts_over_square_zero_thickening R R₀ I hI π hπ hk (F.obj T) (hF T)
  choose B iB aB p hs hp hker hsm using h
  letI := iB
  letI := aB
  have hl : ∀ {T T' : C} (a : T ⟶ T'), ∃ ρ : B T →ₐ[R] B T', ∀ b, p T' (ρ b) = mp F a (p T b) :=
    fun {T T'} a => homLift R R₀ I hI π hπ hk (B T) (F.obj T) (p T) (hs T) (hp T) (hker T)
      (B T') (F.obj T') (p T') (hs T') (hp T') (hker T') (mp F a)
  exact ⟨{ B := fun T => CommAlgCat.of R (B T)
           p := p
           semi := hs
           surj := hp
           ker := hker
           smooth := hsm
           ρ := fun a => (hl a).choose
           nat := fun a b => (hl a).choose_spec b }⟩

end GlobalTheory.Obs
