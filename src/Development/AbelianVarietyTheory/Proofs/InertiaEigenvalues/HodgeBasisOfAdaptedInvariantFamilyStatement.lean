module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeBasisOfAdaptedInvariantFamily
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
open GlobalTheory.HodgeAt


theorem _root_.GlobalTheory.T.hodge_basis_of_adapted_invariant_family : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K K' : FinExt l) (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (w : Fin a → Fin a → P.R.BdR) (k : Fin a → ℤ), (∀ i j, w i j ∈ (P.PD K).Fil (k i)) → (∀ j, ∃ u : Fin a → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i, (ρ g).map (algebraMap (Om l) P.R.BdR) *ᵥ (fun j => P.actQdR (g : GQ l) (w i j)) = w i) → ∃ H : Hodge C ξ ρ K', ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = ∑ i, if k i = n then 1 else 0 := by
  first | (exact @GlobalTheory.HodgeAt.hodge_of_adapted) | (exact GlobalTheory.HodgeAt.hodge_of_adapted) | (intros; apply GlobalTheory.HodgeAt.hodge_of_adapted  <;> assumption)
