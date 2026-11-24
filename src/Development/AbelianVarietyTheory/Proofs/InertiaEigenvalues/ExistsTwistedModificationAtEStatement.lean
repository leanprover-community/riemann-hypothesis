module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedModificationAtE
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

theorem _root_.GlobalTheory.T.exists_twisted_modification_at_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K) (U U' : Matrix (Fin d) (Fin d) (Per.BdR l)) (Λ₀ : Matrix (Fin d) (Fin d) (Per.BdRp l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * (U * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))).map (Per.σD (g : GQ l)) = U * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))) → (∀ m : ℕ, ∃ (k : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) (bk.S)), Λ * Λ' = (l : bk.S) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ ∀ i j, (Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l m) → ∀ N₀ : ℕ, ∃ (N c₂ : ℕ) (X X' : Matrix (Fin d) (Fin d) (bk.S)), N₀ ≤ N ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ (∀ i j, (U * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) ∧ ∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') i j ∈ Per.FilD l N := by
  first | exact @GlobalTheory.BKTwist.exists_twisted_modification | exact GlobalTheory.BKTwist.exists_twisted_modification | (intros; apply GlobalTheory.BKTwist.exists_twisted_modification <;> assumption)
