module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections)
open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.PullPull

section Sections

variable {X Y Z : Scheme.{0}}

theorem pullbackComp_hom_app (b : Z ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : Z.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).hom.app E).app T
        (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) =
      pullbackSections (b ≫ a) E h s := by
  rw [← Vert.DivPull.pullbackComp_inv_app b a E h₁ h₂ h s]
  have e : (Scheme.Modules.pullbackComp b a).inv.app E ≫
      (Scheme.Modules.pullbackComp b a).hom.app E = 𝟙 _ := by simp
  exact congr(($e).app T (pullbackSections (b ≫ a) E h s))

end Sections

section Met

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {E E' : X.Modules} {r : ℕ}

end Met

end GlobalTheory.PullPull

namespace GlobalTheory.VMetric

end GlobalTheory.VMetric
