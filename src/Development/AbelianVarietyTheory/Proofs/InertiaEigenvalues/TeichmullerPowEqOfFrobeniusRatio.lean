module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisMulEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationRadiusLawsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerFurther
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem tc_injective (l : ℕ) [Fact l.Prime] : Function.Injective (tc l) := by
  intro a b hab
  obtain ⟨j, hj⟩ := GlobalTheory.MemLoc.exists_isCrisP l
  have hinj := GlobalTheory.MemLoc.crisP_injective l j hj
  have key : ∀ y : Formalism.Per.Fl l, j (tc l y) =
      algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l)
        (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.tm y)) := by
    intro y
    have := hj.on0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) (Formalism.Per.tm y))
    rw [Subalgebra.coe_algebraMap, ← GlobalTheory.RingIface.tower] at this
    exact this
  have h1 := congrArg j hab
  rw [key, key] at h1
  have h2 := (GlobalTheory.MemLoc.ainf_isDomain_and_injective l).2.2
    (GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective l h1)
  have h3 := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h2
  simpa using h3

theorem teich_eq_of_phi_ratio : ∀ (l : ℕ) [Fact l.Prime] (w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l), w' ≠ 0 →
    φc l (tc l ζ * w') * w' = tc l ζ * w' * φc l w' → ζ ^ l = ζ := by
  intro l _ w' ζ hw h
  have hφ : φc l w' ≠ 0 := ((GlobalTheory.T.acrisValuation_radius_laws l 1 one_pos le_rfl).2.1 w' hw).1
  have hprod : w' * φc l w' ≠ 0 := by
    intro h0
    rcases GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h0 with h0 | h0
    · exact hw h0
    · exact hφ h0
  rw [map_mul, frob_teich] at h
  have h' : (tc l (ζ ^ l) - tc l ζ) * (w' * φc l w') = 0 := by
    linear_combination h
  rcases GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h' with h0 | h0
  · exact tc_injective l (sub_eq_zero.1 h0)
  · exact absurd h0 hprod

end GlobalTheory.PMon.Gauss
