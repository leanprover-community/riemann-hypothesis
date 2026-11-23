module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

noncomputable section
namespace GlobalTheory.HodgeAt

theorem PhiS_act : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (σ : GQ l) (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → ∀ g : ↥(GK K), (∀ y : ↥L.1, (g : GQ l) (σ (y : Om l)) = σ (y : Om l)) → ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a (actVdR (P.PD K) R g x) = ((r g).val.map fun y => algebraMap (Om l) P.R.BdR (σ (y : Om l))) *ᵥ fun i => P.actQdR (g : GQ l) (PhiS P σ L a x i) := by
  intro l _ P K L σ a r R hR g hg x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, PhiS_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero _).symm
  | add x y hx hy =>
    rw [map_add (f := _), PhiS_add, hx, hy, PhiS_add]
    rw [← Matrix.mulVec_add]
    congr 1
    ext i
    simp only [Pi.add_apply, map_add]
  | tmul v b =>
    rw [GlobalTheory.DRFil.actVdR_tmul, P.PD_actdR, hR, PhiS_tmul, PhiS_tmul]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]

    simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum, map_mul, Finset.sum_mul,
    P.actQdR_Om, hg, mul_assoc]

end GlobalTheory.HodgeAt
