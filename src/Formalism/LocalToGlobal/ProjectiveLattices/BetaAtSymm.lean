module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.Analysis.SpecialFunctions.Log.Base
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

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open AlgebraicGeometry CategoryTheory

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

section At

variable {R : Type} [CommRing R] [IsDomain R]

def PsiCoord (D : DegPre R) (χ : D.X) (r : R) : Prop :=
  ∃ (j : PUnit → D.P.L.ι) (_ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit))
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j),
    ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val

def vPsiAt (D : DegPre R) {C : Type} [NormedField C] (f : R →+* C) (p : ℕ) (χ : D.X) : ℝ :=
  open Classical in
  if h : ∃ r, PsiCoord D χ r then -Real.logb p ‖f h.choose‖ else 0

def betaAt (D : DegPre R) {C : Type} [NormedField C] (f : R →+* C) (p : ℕ) (a b : D.X) : ℝ :=
  vPsiAt D f p (a + b) - vPsiAt D f p a - vPsiAt D f p b

theorem betaAt_symm (D : DegPre R) {C : Type} [NormedField C] (f : R →+* C) (p : ℕ) (a b : D.X) :
    betaAt D f p a b = betaAt D f p b a := by
  unfold betaAt
  rw [add_comm a b]
  ring

end At

end Formalism.L2.Pj
