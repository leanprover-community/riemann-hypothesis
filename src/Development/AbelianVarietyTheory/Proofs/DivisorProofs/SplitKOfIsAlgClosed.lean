module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.HtGen

attribute [local instance] Over.cartesianMonoidalCategory

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end Cover

section Chars

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

abbrev TorsK {K : Type} [Field K] (ξ : Sp K ⟶ X) (q : ℕ) : Subgroup (Over.mk ξ ⟶ t.G) := (powMonoidHom q).ker



variable {t} in
def InducedBy {K : Type} [Field K] {ξ : Sp K ⟶ X} {q : ℕ} (χ : TorsK t ξ q →* Kˣ) {R : Type} [CommRing R]
    (x : Sp R ⟶ X) (u : R →+* K) {O : Type} [CommRing O] (ψ : R →+* O) {z : Sp O ⟶ X} (c : TorsChar t z q) : Prop :=
  ∀ (σ : Over.mk x ⟶ t.G) (k : TorsK t ξ q) (a : R) (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G),
    σ ^ q = 1 → k.1.left = spMap u ≫ σ.left → w.left = spMap ψ ≫ σ.left → u a = χ k → (c.χ O w : O) = ψ a

end Chars

end GlobalTheory.HtGen
