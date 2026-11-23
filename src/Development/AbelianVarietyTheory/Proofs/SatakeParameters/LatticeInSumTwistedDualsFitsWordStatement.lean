module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeInSumTwistedDualsFitsWord
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.lattice_in_sum_twisted_duals_fits_word : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x s => Ms x s) → Fits W T (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.fits_of_isSubOfSums | exact GlobalTheory.HTW.Rec.fits_of_isSubOfSums | (intros; apply GlobalTheory.HTW.Rec.fits_of_isSubOfSums <;> assumption)
