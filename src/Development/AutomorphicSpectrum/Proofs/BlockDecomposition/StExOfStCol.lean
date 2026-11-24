module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
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

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

theorem stEx_of_stCol : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StEx := by
  intro hcol R _ C _ F T hG s
  obtain ⟨hι, hdv, hinj, hex0, hex⟩ := hcol R C F T hG
  induction s with
  | zero =>
    intro k j hsk x hv hd
    have hjk : j = k := by omega
    subst hjk
    obtain ⟨z, hz⟩ := (hex0 j x).1 hv
    refine ⟨z, ?_, ⟨rfl, hz⟩⟩
    apply hinj (j + 1)
    rw [← hι, hz, hd, map_zero]
  | succ s ih =>
    intro k j hsk x hv hd
    obtain ⟨a, ha⟩ := (hex s k x).1 hv
    have h1 : T.dvC s (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0 := by
      rw [map_zsmul, ← hdv, ha, hd, smul_zero]
    have h2 : d (T.K s) (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0 := by
      rw [map_zsmul, d_d, smul_zero]
    obtain ⟨z, hz, hst⟩ := ih (k + 1) j (by omega) _ h1 h2
    exact ⟨z, hz, ⟨a, ha, hst⟩⟩

end GlobalTheory.CompanionTheory.EdgeStair
