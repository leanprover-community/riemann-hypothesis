module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameCocycleFrobeniusTwistOnDisc
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
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.semistablePeriod_frameCocycle_frobenius_twist_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (ε : Matrix (Fin d) (Fin d) (Ainf l)), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ → G (bk.iS bk.E) ^ s.N • (V.map i * ε.map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (V.map i).map G) → G (bk.iS (frobS l bk.a bk.E)) ^ s.N • ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i * (ε.map WittVector.frobenius).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ s.N • (s.κ g * ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i).map G) := by
  first | (exact @GlobalTheory.BKLim.FrobTwistKappa.main) | (exact GlobalTheory.BKLim.FrobTwistKappa.main) | (intros; apply GlobalTheory.BKLim.FrobTwistKappa.main  <;> assumption)
