module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeStructureOfAdaptedInvariantFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.GalAdapted

theorem gal_V : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → (ρ g).map ((aDp l).comp (Per.zA l)) * H.V.map (Per.σDp (g : GQ l)) * Matrix.diagonal (fun j => aDp l w ^ H.p j) = aDp l w ^ H.q • H.V := by
  intro l _ K bk C d ρ H g w hw
  have hinj : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := (BdRField.bdR_isField l).2.1
  obtain ⟨u, hu, -⟩ := AdaptedHodge.xi_unit_fil C (bk.ev bk.E) bk.span_ev
  have hΞ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E))) := hu ▸ u.isUnit
  have hξ : Per.σD (g : GQ l) (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) := by
    rw [ActLaws.σD_alg, ActLaws.σDp_aDp, hw, map_mul, map_mul]
  have hmap : ∀ z : ℤ_[l], C.o (zOm l z) = aDp l (Per.zA l z) := fun z => C.o_sec.z z
  have hinv := H.inv g g.2
  ext i j
  apply hinj
  refine (hΞ.pow (H.p j)).mul_left_cancel ?_
  have hσ : ∀ k, (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w)) ^ H.q *
      Per.σD (g : GQ l) (H.Q k j) = (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w)) ^ H.p j *
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp (g : GQ l) (H.V k j)) := by
    intro k
    have := congrArg (Per.σD (g : GQ l)) (H.Q_eq k j)
    rw [map_mul, map_pow, hξ, ActLaws.σD_alg, map_mul, map_pow, ActLaws.σDp_aDp, hw, map_mul, map_mul, map_pow, map_mul] at this
    rw [this]
  have hI : ∑ k, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (ρ g i k))) * Per.σD (g : GQ l) (H.Q k j) = H.Q i j := by
    have := congrFun (congrFun hinv i) j
    simpa [Matrix.mul_apply, hmap] using this
  rw [Matrix.mul_diagonal, Matrix.smul_apply]

  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, RingHom.comp_apply,
  map_mul, map_sum, map_pow]
  have e1 : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p j *
      (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (H.V i j)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) ^ H.q *
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * H.Q i j) := by
    rw [H.Q_eq i j, map_mul, map_pow]; ring
  rw [e1, ← hI]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination -(algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (ρ g i k)))) * hσ k

end GlobalTheory.BKLim.GalAdapted
