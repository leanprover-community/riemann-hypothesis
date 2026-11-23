module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem slice_holds : Slice := by
  intro hP l _ k _ _ hl d X p hSP hR G y
  obtain ⟨hprop, hsm⟩ := hSP
  haveI := hprop
  obtain ⟨hdiag, hpt⟩ := hP k d p inferInstance hsm
  obtain ⟨hy, hpb⟩ := hpt y
  have hunitX : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hunit : IsUnit ((l : Γ(S k, ⊤))) := by
    simpa [map_natCast] using hunitX.map (y.1.appTop).hom
  simp only [GysQ.diag, GysQ.pt, GysQ.cls, dif_pos hdiag, dif_pos hy]
  rw [G.nat hy hdiag (slice y) y.1
    (by rw [slice, ← Category.assoc, pullback.lift_fst, Category.id_comp]) hpb]
  congr 1
  first
  | exact hR.one_nat y.1 hunitX
  | exact hR.one_nat y.1 hunit

end UpperTheory.Gal.KunnethLefschetz
