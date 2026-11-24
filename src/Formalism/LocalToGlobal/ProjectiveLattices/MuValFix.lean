module

public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem MuVal.eq_one_of_fixed {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ}
    (h : MuVal V χ mu) (y : (AE D)ˣ)
    (hy : sigR (AF D.host.F) D.sp.cm.sig (y : AE D) = y) : χ y = 1 := by
  obtain ⟨x, hx⟩ := h.1 1
  have hxy : IsDetRoot V 1 (x * y) := by
    unfold IsDetRoot at hx ⊢
    rw [Units.val_mul, map_mul, hy, ← mul_assoc, ← hx]
  have e2 := h.2 1 (x * y) hxy
  rw [h.2 1 x hx, map_mul] at e2
  have e3 : χ x * 1 = χ x * χ y := by
    apply Subtype.ext
    simpa [Circle.coe_mul] using e2
  exact (mul_left_cancel e3).symm

end Formalism.L2.Pj
