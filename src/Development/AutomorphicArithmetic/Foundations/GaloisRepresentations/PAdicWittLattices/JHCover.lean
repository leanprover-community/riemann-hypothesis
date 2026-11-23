module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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

open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.G3

theorem jHCover : PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cover := by
  intro k _ X s _
  haveI : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from s]; infer_instance⟩
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  let C := X.affineCover.finiteSubcover
  let e := Fintype.equivFin C.I₀
  refine ⟨Fintype.card C.I₀, fun i => (C.f (e.symm i)).opensRange, ?_, ?_⟩
  · rw [e.symm.surjective.iSup_comp (fun j => (C.f j).opensRange)]
    exact C.iSup_opensRange
  · intro S hS
    have h := IsAffineOpen.biInf (X := X) (S : Set (Fin (Fintype.card C.I₀))) S.finite_toSet
      (Finset.coe_nonempty.mpr hS) (U := fun i => (C.f (e.symm i)).opensRange)
      (fun i _ => isAffineOpen_opensRange _)
    simpa only [Finset.mem_coe] using h

end UpperTheory.Gal.G3
