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

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem hPull_omega_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) (a j : ℕ)
    (y : Sheaf.H.{0} ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j),
    (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).symm (hPull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j y) =
      pullC u hu a j ((GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm y) := by
  intro K _ X Y q p u hu a j y
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  rw [AddEquiv.apply_symm_apply]
  obtain ⟨w, rfl⟩ := (GlobalTheory.SiteCoh.terminalEquiv ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j
    isTerminalTop).surjective y
  obtain ⟨z, rfl⟩ := (GlobalTheory.cohOn.toH' (GlobalTheory.HodgeCoh.Omega p a) ⊤ j).surjective w
  have hz : (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm
      (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)) = z :=
    (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm_apply_apply z
  rw [hz]
  change GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop
      (GlobalTheory.SheafPull.pull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j (homOfLE le_top)
        ((GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop).symm
          (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)))) =
    GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ _ j (GlobalTheory.HodgeCoh.hodgePull hu a j z))
  rw [AddEquiv.symm_apply_apply]
  congr 1

end CrystallineSemistableComparison.Om.Cech
