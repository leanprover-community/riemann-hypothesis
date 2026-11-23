module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapsSurjectiveWithKernelsStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfectAlg

theorem exists_theta_mod {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    ∃ θ : A.Acr n →+* A.Un n, (∀ x : A.W, θ (A.toAcr n x) = Ideal.Quotient.mk _ (A.th x)) ∧
      RingHom.ker θ = A.Fil n 1 := by
  obtain ⟨hsurj, hker, -, -⟩ := GlobalTheory.T.quotient_maps_surjective_with_kernels A n
  refine ⟨((Ideal.quotEquivOfEq hker).toRingHom.comp
      (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom).comp
      (Ideal.Quotient.mk (A.Fil n 1)), fun x => ?_, ?_⟩
  · have h1 : A.uToQ n (A.th x) = Ideal.Quotient.mk (A.Fil n 1) (A.toAcr n x) := by rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← h1, ← RingHom.quotientKerEquivOfSurjective_apply_mk hsurj, RingEquiv.symm_apply_apply,
      Ideal.quotEquivOfEq_mk]
  · ext y
    simp only [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [map_eq_zero_iff _ (RingEquiv.injective _), map_eq_zero_iff _ (RingEquiv.injective _),
      Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.CompanionTheory.PerfectAlg
