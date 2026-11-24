module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace UnivPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def pol (Xo : Moduli D l) : PolAV Xo.X := GlobalTheory.Obj.toPolAV Xo.univ

theorem smooth (Xo : Moduli D l) : Smooth Xo.s :=
  haveI := Xo.smooth
  SmoothOfRelativeDimension.smooth D.dim Xo.s

theorem isLocallyNoetherian (Xo : Moduli D l) : IsLocallyNoetherian Xo.X := by
  haveI := smooth Xo
  exact LocallyOfFiniteType.isLocallyNoetherian Xo.s

theorem isReduced (Xo : Moduli D l) : IsReduced Xo.X := by
  haveI := smooth Xo
  exact GlobalTheory.isReduced_of_smooth_of_isReduced Xo.s

theorem isUnit_natCast (Xo : Moduli D l) (n : ℕ) (hn : 0 < n) : IsUnit (n : Γ(Xo.X, ⊤)) := by
  have hK : IsUnit (n : KA l) := by
    haveI : CharZero (KA l) := (RingHom.charZero_iff (algebraMap (KA l) ℂ).injective).2 inferInstance
    exact (isUnit_iff_ne_zero).2 (Nat.cast_ne_zero.2 hn.ne')
  have hΓ := hK.map ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom)
  have hX := hΓ.map Xo.s.appTop.hom
  simpa using hX

end UnivPol

theorem moduli_univ_polAV :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), IsLocallyNoetherian Xo.X ∧ IsReduced Xo.X ∧ (∀ n : ℕ, 0 < n → IsUnit (n : Γ(Xo.X, ⊤))) ∧ IsAbelianScheme Xo.univ.t.G ∧ ∀ (p : ∀ (A : Over Xo.X) [GrpObj A] [IsCommMonObj A], LB A.left → ℕ → Prop), (∀ P : PolAV Xo.X, p P.A P.L P.g) → p Xo.univ.t.G Xo.univ.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l Xo
  exact ⟨UnivPol.isLocallyNoetherian Xo, UnivPol.isReduced Xo, UnivPol.isUnit_natCast Xo,
    ObjDim.isAbelianScheme Xo.univ, fun p h => h (UnivPol.pol Xo)⟩

end GlobalTheory
