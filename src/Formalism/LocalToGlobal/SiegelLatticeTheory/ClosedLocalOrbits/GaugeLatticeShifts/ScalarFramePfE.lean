module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

def IotaG (q : E) (abelian₂ : Submodule M.L.O V) {r : ℕ} (f₀ f₁ f₂ : Fin (r + 1) → V) (e : V ≃ₗ[E] V) : Prop :=
  (∀ x x' : V, x ∈ abelian₂ → x' ∈ abelian₂ → x ∈ H.perp (H.X f₀) → x' ∈ H.perp (H.X f₁) → x - x' ∈ H.smulLat q abelian₂ →
    ∃ y y'' : V, y ∈ abelian₂ ∧ y'' ∈ abelian₂ ∧ y ∈ H.perp (H.X f₀) ∧ y'' ∈ H.perp (H.X f₂) ∧ x - y ∈ H.X f₀ ∧
      e x' - y'' ∈ H.X f₂ ∧ y - y'' ∈ H.smulLat q abelian₂) ∧
  (∀ x x'' : V, x ∈ abelian₂ → x'' ∈ abelian₂ → x ∈ H.perp (H.X f₀) → x'' ∈ H.perp (H.X f₂) →
    x - x'' ∈ H.smulLat q abelian₂ →
    ∃ y y' : V, y ∈ abelian₂ ∧ y' ∈ abelian₂ ∧ y ∈ H.perp (H.X f₀) ∧ y' ∈ H.perp (H.X f₁) ∧ x - y ∈ H.X f₀ ∧
      e.symm x'' - y' ∈ H.X f₁ ∧ y - y' ∈ H.smulLat q abelian₂)

end Generic

end Formalism.L2.SG.Pf.ScalarFramePf
