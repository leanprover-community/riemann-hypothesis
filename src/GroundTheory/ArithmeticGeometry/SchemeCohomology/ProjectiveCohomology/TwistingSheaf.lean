module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwist
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Linear
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory TopologicalSpace MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

def IsCoherent {X : Scheme.{u}} (F : X.Modules) : Prop :=
  F.IsQuasicoherent ∧ ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U)

abbrev algebraOfOver (X : Scheme.{u}) (A : Type u) [CommRing A] [X.Over (Spec (.of A))] :
    Algebra A Γ(X, ⊤) :=
  overAlgebra (CommRingCat.of A)

namespace ProjSpace

variable (A : Type u) [CommRing A] (n : ℕ)

def toSpecBase : projectiveSpace A n ⟶ Spec (.of A) :=
  Proj.toSpecZero (grading A n) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (grading A n 0)))

instance overSpec : (projectiveSpace A n).Over (Spec (.of A)) := ⟨toSpecBase A n⟩

variable {A n}

def twist (G : (projectiveSpace A n).Modules) (k : ℤ) : (projectiveSpace A n).Modules :=
  G ⊗ twistingSheaf (grading A n) k

end ProjSpace

namespace ProjScheme

variable {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}} (i : X ⟶ projectiveSpace A n)

def twistingSheaf (k : ℤ) : X.Modules :=
  (Scheme.Modules.pullback i).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)

def twist (F : X.Modules) (k : ℤ) : X.Modules :=
  F ⊗ twistingSheaf i k

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
