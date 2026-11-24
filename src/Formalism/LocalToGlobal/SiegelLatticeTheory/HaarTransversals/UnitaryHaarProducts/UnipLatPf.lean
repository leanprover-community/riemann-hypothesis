module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipLat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.ZLattice.Basic

@[expose] public section

open NumberField NumberField.InfinitePlace

namespace Formalism.L2.SG.Pf

theorem oeApprox_holds : Formalism.L2.SG.Pf.UnipLat.OEApprox := by
  intro F E _ _ _ _ _ _ hE _ φ hφ
  classical

  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
    (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis E))
  refine ⟨R, fun t => ?_⟩

  let w : InfinitePlace F → InfinitePlace E := fun v => InfinitePlace.mk (φ v)
  have hw : ∀ v, (w v).comap (algebraMap F E) = v := by
    intro v
    have hcomp : (φ v).comp (algebraMap F E) = v.embedding := RingHom.ext (hφ v)
    simp only [w, InfinitePlace.comap_mk, hcomp, InfinitePlace.mk_embedding]
  have hinj : ∀ v v', w v = w v' → v = v' := by
    intro v v' h
    rw [← hw v, ← hw v', h]
  let c : InfinitePlace F → ℂ := fun v =>
    if (w v).embedding = φ v then t v else (starRingEnd ℂ) (t v)
  let x : mixedEmbedding.mixedSpace E :=
    (0, fun u => if h : ∃ v, u.1 = w v then c h.choose else 0)
  have hmem : x - ZSpan.fract (mixedEmbedding.latticeBasis E) x ∈
      mixedEmbedding.integerLattice E := by
    rw [← mixedEmbedding.mem_span_latticeBasis, ZSpan.fract_apply, sub_sub_cancel]
    exact (ZSpan.floor _ x).2
  obtain ⟨m, hm⟩ := hmem
  have hm' : mixedEmbedding E (m : E) = x - ZSpan.fract (mixedEmbedding.latticeBasis E) x := hm
  refine ⟨m, fun v => ?_⟩
  have hc : (w v).IsComplex := hE.isComplex (w v)
  let u : {u : InfinitePlace E // u.IsComplex} := ⟨w v, hc⟩
  have hxu : x.2 u = c v := by
    have hex : ∃ v', u.1 = w v' := ⟨v, rfl⟩
    show (if h : ∃ v', u.1 = w v' then c h.choose else 0) = c v
    rw [dite_eq_left hex, hinj _ _ hex.choose_spec.symm]
  have hfr : x - mixedEmbedding E (m : E) = ZSpan.fract (mixedEmbedding.latticeBasis E) x := by
    rw [hm', sub_sub_cancel]
  have hval : (ZSpan.fract (mixedEmbedding.latticeBasis E) x).2 u
      = c v - (w v).embedding (m : E) := by
    rw [← hfr, Prod.snd_sub, Pi.sub_apply, hxu, mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hb : ‖c v - (w v).embedding (m : E)‖ ≤ R := by
    rw [← hval]
    exact ((norm_le_pi_norm _ u).trans (norm_snd_le _)).trans
      (hR _ (ZSpan.fract_mem_fundamentalDomain _ x))
  by_cases h : (w v).embedding = φ v
  · have hcv : c v = t v := if_pos h
    rw [hcv, h] at hb
    exact hb
  · have h2 : (w v).embedding = ComplexEmbedding.conjugate (φ v) :=
      (InfinitePlace.embedding_mk_eq (φ v)).resolve_left h
    have hcv : c v = (starRingEnd ℂ) (t v) := if_neg h
    rw [hcv, h2, ComplexEmbedding.conjugate_coe_eq, ← map_sub, Complex.norm_conj] at hb
    exact hb

end Formalism.L2.SG.Pf
