module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory

theorem addGroupFG_sec_of_isArithVar : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ B : LB X, B.IsLB → AddGroup.FG B.Sec := by
  intro k _ X _ p D h B hB
  letI : Algebra k Γ(X, ⊤) :=
    ((Scheme.Hom.appTop p).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  have hf : ∀ r : k, algebraMap k Γ(X, ⊤) r =
      (Scheme.Hom.appTop p) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r) := fun _ => rfl
  haveI := h.finite
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hfin : Module.Finite k (coh (twist (QCoh.structureModule X) B) 0) :=
    finite_coh_twist_of_isProjOver hf (QCoh.structureModule X) h.isProjOver hB 0
  haveI : Module.Finite ℤ (coh (twist (QCoh.structureModule X) B) 0) := Module.Finite.trans k _
  have hfg : AddGroup.FG (coh (twist (QCoh.structureModule X) B) 0) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  exact AddGroup.fg_of_surjective (f := (cohZeroTwistEquiv B).toAddEquiv.toAddMonoidHom)
    (cohZeroTwistEquiv B).toAddEquiv.surjective

end GlobalTheory
