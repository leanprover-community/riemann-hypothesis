module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedRingOfIntegers
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

section Alg

variable {S : Type} [CommRing S] {ρ V : Type}

def apolar (P : MvPolynomial V S) (f : MvPowerSeries V S) : S :=
  ∑ m ∈ P.support, P.coeff m * ((m.prod fun _ n => (n.factorial : S)) * MvPowerSeries.coeff m f)

theorem apolar_monomial (m : V →₀ ℕ) (c : S) (f : MvPowerSeries V S) :
    apolar (MvPolynomial.monomial m c) f = c * ((m.prod fun _ n => (n.factorial : S)) * MvPowerSeries.coeff m f) := by
  classical
  rw [apolar, Finset.sum_subset (MvPolynomial.support_monomial_subset) fun x _ hx => by
    rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul], Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

end Alg

section Exp

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (a : OAct O G)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {ρ V : Type} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
  (ch : ρ → O →+* S)

variable (bar : O → O) (L : LB G.left) (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => eSec G) fun _ => 1))


variable (G) in
abbrev Pw (n : ℕ) : Over X := Over.mk x0 ⊗ powObj G n


variable (G) in
abbrev pr {n : ℕ} (b : Fin n) : (Pw G x0 n).left ⟶ G.left := (snd _ _ ≫ powPr G b).left

end Exp

section Gt

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} (Y : Ray oa)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ Sp R) {ρ V : Type} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
  (ch : ρ → O →+* S)

end Gt

end GlobalTheory.RayEv
