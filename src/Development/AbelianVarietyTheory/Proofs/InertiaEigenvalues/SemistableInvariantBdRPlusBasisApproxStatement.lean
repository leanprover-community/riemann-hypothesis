module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableInvariantBdRPlusBasisApprox
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

theorem _root_.GlobalTheory.T.semistable_invariant_bdRPlus_basis_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) (k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), Mn ^ d = 0 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∀ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) → ∃ Λ₀ : Matrix (Fin d) (Fin d) (Per.BdRp l), (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * (U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))).map (Per.σD (g : GQ l)) = U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) (bk.S)), Λ * Λ' = (l : bk.S) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ ∀ i j, (Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.SstPer.SFil.invariant_basis_approx) | (exact GlobalTheory.SstPer.SFil.invariant_basis_approx) | (intros; apply GlobalTheory.SstPer.SFil.invariant_basis_approx  <;> assumption)
