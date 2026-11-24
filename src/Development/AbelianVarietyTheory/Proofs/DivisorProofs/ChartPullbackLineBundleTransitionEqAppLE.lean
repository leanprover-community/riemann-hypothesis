module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem chartPull_g_appLE : ∀ (Y Y' : Scheme.{0}) (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) (cp : ChartPull A' A h) (i j : A'.ι), ((A'.g i j : Γ(Y', A'.U i ⊓ A'.U j)ˣ) : Γ(Y', A'.U i ⊓ A'.U j)) = (h.appLE (A.U (cp.idx i) ⊓ A.U (cp.idx j)) (A'.U i ⊓ A'.U j) (le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j)))).hom ((A.g (cp.idx i) (cp.idx j) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))ˣ) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))) := by
  intro Y Y' A' A h cp i j
  have e : A'.U i ⊓ A'.U j ≤ h ⁻¹ᵁ (A.U (cp.idx i) ⊓ A.U (cp.idx j)) :=
    le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j))
  apply TopCat.Presheaf.section_ext Y'.sheaf (A'.U i ⊓ A'.U j)
  intro y hy
  have h1 := congrArg Units.val (cp.g y i j hy.1 hy.2)
  rw [gm_val _ y _ hy, gm_val h y _ (e hy)] at h1
  refine h1.trans ?_
  show _ = (Y'.presheaf.germ _ y hy).hom ((Y'.presheaf.map (homOfLE e).op).hom ((h.app _).hom _))
  exact (TopCat.Presheaf.germ_res_apply Y'.presheaf _ y hy _).symm

end GlobalTheory
