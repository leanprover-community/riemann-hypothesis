module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevels
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatConj

theorem xiR_val {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (t : T0) (PP : Pl D.host.E) (hP : PP ∈ R.Q t) (u : (kP PP)ˣ) :
    ∃ s : (AE D)ˣ, ((R.xiR t PP u : ℂˣ) : ℂ) = ((R.xi t s : Circle) : ℂ) := by
  obtain ⟨a, k, hk, hx⟩ := GlobalTheory.ConjRes.exists_lift PP u
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 PP
  refine ⟨Formalism.L2.JoinChr.locU he.1 k, ?_⟩
  rw [hC.lev.xiR t PP hP a k u hk hx, (hC.lev.xi t).2 PP e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)]

theorem prod_val {D : D7} (ξ : (AE D)ˣ →* Circle) (S : Finset (Pl D.host.E)) (v : Pl D.host.E → ℂ)
    (hv : ∀ PP ∈ S, ∃ s : (AE D)ˣ, v PP = ((ξ s : Circle) : ℂ)) :
    ∃ s : (AE D)ˣ, ∏ PP ∈ S, v PP = ((ξ s : Circle) : ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a S ha ih =>
    obtain ⟨s0, h0⟩ := hv a (Finset.mem_insert_self a S)
    obtain ⟨s1, h1⟩ := ih fun PP hP => hv PP (Finset.mem_insert_of_mem hP)
    refine ⟨s0 * s1, ?_⟩
    rw [Finset.prod_insert ha, h0, h1, map_mul, Circle.coe_mul]

end GlobalTheory.FlatConj
