module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

@[expose] public section
-- `Sheaf.H` and `HasExt` are stated for `sheafIsAbelian`; erase the definitionally equal
-- `TopCat.Sheaf.instAbelian` so the kernel does not have to unfold both to compare them.
attribute [-instance] TopCat.Sheaf.instAbelian

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechDelta

theorem terminalEquiv_δ {X : TopCat.{0}} {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (n : ℕ)
    (y : Sheaf.H'.{0} S.X₃ n (⊤ : Opens X)) :
    GlobalTheory.SiteCoh.terminalEquiv S.X₁ (n + 1) isTerminalTop (GlobalTheory.SheafLES.δ hS n ⊤ y) =
      H.δ hS n (n + 1) rfl (GlobalTheory.SiteCoh.terminalEquiv S.X₃ n isTerminalTop y) := by
  exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (GlobalTheory.SiteCoh.freeSheafIsoConst isTerminalTop).inv) y hS.extClass (zero_add n) rfl (by omega)).symm

theorem hPull_δ {X Y : TopCat.{0}} (f : X ⟶ Y) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (α : S ⟶ S'.map (push f)) (n : ℕ) (x : Sheaf.H.{0} S.X₃ n) :
    hPull f α.τ₁ (n + 1) (H.δ hS n (n + 1) rfl x) = H.δ hS' n (n + 1) rfl (hPull f α.τ₃ n x) := by
  obtain ⟨y, rfl⟩ : ∃ y, GlobalTheory.SiteCoh.terminalEquiv S.X₃ n isTerminalTop y = x :=
    ⟨_, AddEquiv.apply_symm_apply _ x⟩
  rw [← terminalEquiv_δ hS n y]
  dsimp only [hPull, GlobalTheory.SheafPull.pull, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  erw [GlobalTheory.SheafPull.sitePull_δ (TopologicalSpace.Opens.map f) hS hS' α n]
  exact terminalEquiv_δ hS' n _

end GlobalTheory.CompanionTheory.CechDelta
