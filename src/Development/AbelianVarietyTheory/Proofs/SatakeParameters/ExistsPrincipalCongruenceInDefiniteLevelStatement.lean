module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrincipalCongruenceInDefiniteLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_principalCongruence_in_definiteLevel : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J, (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨_, h⟩ = 1 := by
  first | exact @GlobalTheory.VFormCong.exists_cong_levEnv | exact GlobalTheory.VFormCong.exists_cong_levEnv | (intros; apply GlobalTheory.VFormCong.exists_cong_levEnv <;> assumption)
