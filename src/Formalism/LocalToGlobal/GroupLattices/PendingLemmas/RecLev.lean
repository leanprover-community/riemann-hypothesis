module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.PNeZeroOL
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelWithoutExtraPlaces
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CoeffOneLNe

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem
open scoped TensorProduct

namespace Formalism.L2.G.Pend

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record4

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)

variable (hg : ∀ a, D.host.g a ≠ 0) (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))

abbrev levelsL : Levels (fillsL D u h L h5 h2 he r Lc I ψ e c hc) :=
  levelsRec D u h (settingOL p (orderOf (zPsi D.R.toFrame h)) L h5 h2 he) r Lc I ψ (repP Lc p) e c hc hg hpg Cb Sx

variable (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)
  (hst : FinStab (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g)

abbrev sysRec : Sys p :=
  sysL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin

end Record4

end Formalism.L2.G.Pend
