module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaOfDiscCocycle
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


theorem _root_.GlobalTheory.T.exists_beta_of_disc_cocycle_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (φε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (H : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsUnit H → (∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∀ a b, bk.iS bk.E ^ m ∣ (κ g * (Λ.map bk.iS).map G - Λ.map bk.iS) a b) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → G (bk.iS (frobS l bk.a bk.E)) ^ N • (H.map i * (φε g).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ N • (κ g * (H.map i).map G)) → ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) a b, bk.ev bk.E ^ m ∣ (φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) a b := by
  first | (exact @GlobalTheory.BKLim.exists_beta_of_disc_cocycle) | (exact GlobalTheory.BKLim.exists_beta_of_disc_cocycle) | (intros; apply GlobalTheory.BKLim.exists_beta_of_disc_cocycle  <;> assumption)
