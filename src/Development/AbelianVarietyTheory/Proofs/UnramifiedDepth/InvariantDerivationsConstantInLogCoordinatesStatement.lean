module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivationsConstantInLogCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.invariantDerivations_constant_in_logCoordinates : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (n : ℕ) (W : Type) [Fintype W] (Z : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (Z s) = 0) → ∀ (b : Fin n) (u : Fin dd → C) (co : W → C), (∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • MvPowerSeries.pderiv (R := C) w (Z (b', j)) = if b' = b then MvPowerSeries.C (u j) else 0) → ∀ G : PS C n dd, MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) (DofN (Y.B.FK C) b u G) = ∑ w, co w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) G) := by
  first | exact @GlobalTheory.InvDerivLog.subst_ex_DofN | exact GlobalTheory.InvDerivLog.subst_ex_DofN | (intros; apply GlobalTheory.InvDerivLog.subst_ex_DofN <;> assumption)
