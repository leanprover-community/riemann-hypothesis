module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorPowEqSum
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

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.hodgeTateOperator_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (C : Core l) (ξ : Ainf l) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (σ : GQ l) (z : ℂ_[l]) (H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), U * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) → IsHT C ξ (fun g => (r g).val.map σ) z u → ∀ n : ℕ, u ^ n = ∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x) := by
  first | exact @GlobalTheory.BKLim.htOp_pow_eq_sum | exact GlobalTheory.BKLim.htOp_pow_eq_sum | (intros; apply GlobalTheory.BKLim.htOp_pow_eq_sum; all_goals assumption)
