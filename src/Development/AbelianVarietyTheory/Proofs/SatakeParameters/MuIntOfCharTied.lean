module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective
import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.MuIntegral

theorem muInt_of_charTied : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D)
    (Tp : Formalism.L2.Host.TupTied D C nch),
    Formalism.L2.Host.NCharTied D C nch Tp → GlobalTheory.SplitRead.MuInt D.nd D.naut := by
  intro D C nch Tp hT i τ z hz
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hmu := hT.muC i j hjj
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, hn, ho⟩ := Tp.xi_fin (D.nd.mu i)
  have hinf : (Tp.tup (D.nd.mu i) j).HasInfQ (Formalism.L2.Host.embPsi D.host) (fun g => -Formalism.L2.Host.eExp D j g) :=
    (C.isMu0 j).inf.mul_triv (GlobalTheory.TypeValues.inf_eq_one _ hn ho)
  rw [← hmu] at hinf
  have key := hT.infG _ _ hinf
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
  obtain ⟨m, hm⟩ := (D.hc (D.eTau.symm (D.eTau ρ))).e_int j
  have hm' : Formalism.L2.Host.eExp D j (D.eTau ρ) = m := hm
  rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
  · have ht : τ = Formalism.L2.Host.embPsi D.host (D.eTau ρ) := h.symm
    rw [ht, (key (D.eTau ρ)).1] at hz
    refine ⟨-m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring
  · have ht : τ = (starRingEnd ℂ).comp (Formalism.L2.Host.embPsi D.host (D.eTau ρ)) := by
      rw [← h]; ext x; rfl
    rw [ht, (key (D.eTau ρ)).2] at hz
    refine ⟨m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring

end GlobalTheory.MuIntegral
