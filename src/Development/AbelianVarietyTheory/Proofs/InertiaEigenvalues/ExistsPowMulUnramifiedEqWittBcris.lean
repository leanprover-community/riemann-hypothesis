module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWittStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisBasicTheoremsProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.TeichmullerPowerUnit

theorem exists_pow_mul_u_eq_aB : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) ∈ K.1 → ∃ (n : ℕ) (w : Wq l bk.a), (l : Per.Bcris l) ^ n * C.u c = Per.aB l (wA l bk.a w) := by
  intro l _ K bk C c hc
  obtain ⟨n, w, hw⟩ := GlobalTheory.T.exists_prime_pow_mul_eq_theta_witt l K bk (c : Om l) hc c.2
  have ho := GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus l bk.a C w ((l : Om l) ^ n * (c : Om l)) hw
  refine ⟨n, w, ?_⟩
  apply GlobalTheory.Published.FontaineBcris.iotaInj GlobalTheory.T.fontaineBcrisBasicTheorems_proof C
  have hB : C.ι (Per.aB l (wA l bk.a w)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (wA l bk.a w)) :=
    GlobalTheory.MemLoc.ULaws.iota_aB C (wA l bk.a w)
  rw [hB, ← ho, map_mul, map_pow, map_natCast, C.ι_u, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]

end GlobalTheory.TeichmullerPowerUnit
