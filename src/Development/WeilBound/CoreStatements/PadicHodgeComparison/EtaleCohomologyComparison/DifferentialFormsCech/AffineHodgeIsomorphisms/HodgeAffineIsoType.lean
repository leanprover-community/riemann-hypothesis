module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFormsOfFormUniquenessStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.HdgAffIsoOnto
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.OmNatB
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.L2

theorem hodge_affine_iso_sign :
    ∀ (K : Type) [Field K] [CharZero K],
    ∃ (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
      HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (ε : ℕ → ℕ → ℤ), (∀ a b, ε a b = 1 ∨ ε a b = -1) ∧
    (∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q]
      [IsAffine Y] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (x : HT.Hdg p a a),
      e q a (HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e p a x))) ∧
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a b c : ℕ) (h : a + b = c)
      (x : HT.Hdg q a a) (y : HT.Hdg q b b),
      e q c (HT.cupH q h h x y) = ε a b • wedgeOm K (Sec q ⊤) h (e q a x) (e q b y)) ∧
    ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q], e q 0 (HT.oneH q) = oneOm K (Sec q ⊤) :=
  hdg_aff_iso_onto (GlobalTheory.T.affine_forms_of_form_uniqueness CrystallineSemistableComparison.Onto.formUniq_pf) CrystallineSemistableComparison.Onto.omNatB_pf

end CrystallineSemistableComparison.Om.L2
