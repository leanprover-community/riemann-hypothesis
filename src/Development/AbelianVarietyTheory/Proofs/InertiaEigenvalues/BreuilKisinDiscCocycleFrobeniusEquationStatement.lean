module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscCocycleFrobeniusEquation
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_disc_cocycle_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev) → (Y.map bk.iA).det ≠ 0 → ∀ (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (w : (Ainf l)ˣ), Per.σA g (bk.ev bk.E) = bk.ev bk.E * w → ∀ (P : Matrix (Fin d) (Fin d) (Ainf l)), P.map WittVector.frobenius = P → ∀ (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA) → bk.iS bk.E ^ (2 * N) • e = (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA := by
  first | (exact @GlobalTheory.BSP.CocycleFrob.frob_eq) | (exact GlobalTheory.BSP.CocycleFrob.frob_eq) | (intros; apply GlobalTheory.BSP.CocycleFrob.frob_eq  <;> assumption)
