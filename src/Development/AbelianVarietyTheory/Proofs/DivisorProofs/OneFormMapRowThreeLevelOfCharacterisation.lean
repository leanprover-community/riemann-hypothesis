module

public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAlStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllTuplesOverCoreOfRankBoundStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRow3

theorem oneFormMapRow_threeLevel_of_characterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.WeakCharacterisation F → R.toRealDat.ExAt → Nonempty (FWTie T R.toRealDat κ v₀) → IoExt R.toRealDat → ∀ i, OMPins T R.toRealDat κ v₀ O i → PhaseTie T R.toRealDat κ v₀ O ph i → OneMapRowR T R.toRealDat κ v₀ O ph i := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O ph hn hC hE hFW hIo i hP hT
  obtain ⟨hcore, hoff, hused⟩ := GlobalTheory.T.hk3Core_and_tup_mu_of_weakCharacterisation D G Pl0 I0 T0 A3 T.Q.c.F R F hC hE
  exact GlobalTheory.T.oneMap_all_tuples_over_core_of_rankBound D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O ph hn hcore hoff hused hFW hIo i hP hT

end GlobalTheory.OneMapRow3
