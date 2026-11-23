module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormCupWedge
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

theorem _root_.GlobalTheory.T.hodge_form_cup_wedge : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y) := by
  first | exact @GlobalTheory.CompanionTheory.OmCup.main | exact GlobalTheory.CompanionTheory.OmCup.main | (intros; apply GlobalTheory.CompanionTheory.OmCup.main <;> assumption)
