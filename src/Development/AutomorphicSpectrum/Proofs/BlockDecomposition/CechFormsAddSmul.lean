module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCech

theorem cechOmAdd_smul {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j) :
    cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x := by
  letI := GlobalTheory.HodgeCoh.algΓ q
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  have h1 : ∀ z : CO q U a j, GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j (cechOmAdd q U hU hUaff a j z) =
      cechHAddEquivH.{0} U hU hUaff (GlobalTheory.HodgeCoh.Omega q a) j z :=
    fun z => (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).apply_symm_apply _
  have h2 := cechHAddEquivH_naturality.{0} U hU hUaff
    (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j x
  have h3 := GlobalTheory.coh.toH_map K (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j
    (cechOmAdd q U hU hUaff a j x)
  rw [h1] at h3 ⊢
  exact h2.trans h3.symm

end GlobalTheory.CompanionTheory.OmCech
