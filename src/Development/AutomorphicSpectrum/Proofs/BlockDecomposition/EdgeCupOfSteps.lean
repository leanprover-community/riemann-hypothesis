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

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem edgeCup_of_steps : CrystallineSemistableComparison.E.CupCls → CrystallineSemistableComparison.E.StTop → CrystallineSemistableComparison.E.StCupA → CrystallineSemistableComparison.E.StCupB → CrystallineSemistableComparison.E.EdgeCup := by
  intro hCls hTop hA hB
  unfold CrystallineSemistableComparison.E.EdgeCup
  intro R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n hn x y a b hx hy
  obtain ⟨z, hz, hzx, rfl⟩ := hx
  obtain ⟨z', hz', hzy, rfl⟩ := hy
  obtain ⟨hu, hcls⟩ := hCls R C F₁ F₂ F₃ P i j n hn z z' hz hz'
  refine ⟨P.cupC hn z z', hu, ?_, hcls.symm⟩
  have hyy := hTop R C F₂ T₂ hT₂ j z' hz' j 0 y hzy
  have hb := hB R C F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n hn z z' hz j 0 i (add_zero i) y hzy
  exact hA R C F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n z y (P.cupC hn z z') hyy.1 hyy.2 hb i 0 n hn x hzx

end GlobalTheory.CompanionTheory.EdgeMap
