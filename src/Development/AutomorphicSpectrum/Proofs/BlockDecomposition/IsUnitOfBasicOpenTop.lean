module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B CrystallineSemistableComparison.Pb DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.KMVan

section Sc

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']

structure Sc (Φ : PDF R C) (Λ : Type) [CommRing Λ] where
  ρ : ∀ T : C, Λ →+* Φ.A.obj T
  nat : ∀ {T T' : C} (φ : T ⟶ T') (a : Λ), (Φ.A.map φ).hom (ρ T a) = ρ T' a

variable {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end Sc

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section Loc
open TensorProduct
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end Loc
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section D
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end D
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section LT
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end LT
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section FV
variable {R : Type} [CommRing R]

end FV
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section PS
open CrystallineSemistableComparison.Pb.Site GlobalTheory.PDA GlobalTheory.CompanionTheory.ChartLocBc
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

end PS

section Res
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

end Res

section Fr
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

end Fr
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section CL
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V V' : X.Opens} {d : ℕ}

end CL
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU (⊤ : X.Opens) T := fun _ _ => trivial

def evT (T : Thick (nlFun γ p X q κ)) : Γ(X, ⊤) →+* T.B ⧸ T.J := ev T (inU_top T)

theorem evT_nat {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (f : Γ(X, ⊤)) :
    evT T' f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X)
      (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ ⊤), GlobalTheory.Cris.evalAt y ⊤ hh f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) (inU_top T) hh f
  exact key _ (pt_hom φ) (inU_top T')

end TAU
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU2
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

end TAU2
end GlobalTheory.CompanionTheory.KMVan
